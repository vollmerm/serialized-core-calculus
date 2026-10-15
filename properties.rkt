#lang racket

;; The metatheory, run as properties.
;;
;; Each section states a property of the calculus and checks it on sampled
;; inputs.  Where a property is about syntax alone, `redex-check` samples the
;; grammar directly.  Where it is about programs, the grammar is useless as a
;; source: almost every term it produces fails typing at its first resource
;; binder, so the property would pass vacuously.  Two generators supply real
;; inputs instead -- `random-shape` builds well-formed shapes, and
;; `copy-program` builds a closed, well-typed program for any such shape.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "layout.rkt"
         "protocol.rkt"
         "capability.rkt"
         "syntax.rkt"
         "match.rkt"
         "typing.rkt"
         "machine.rkt"
         "examples.rkt"
         "span-candidate.rkt")

(provide (all-defined-out))

;; ---------------------------------------------------------------------------
;; Generators
;; ---------------------------------------------------------------------------

;; Closed shapes, which is all well-formedness asks.  With `allow-rec?`, a
;; datatype's right constructor may recur; its left one never does, so every
;; generated shape has finite values and `random-value` can always stop.
;; Binders are numbered by depth, so a field can recur through an outer
;; datatype as well as its own.
(define (random-shape depth #:allow-rec? [allow-rec? #t] [scope '()])
  (define (fields n rec?)
    (for/list ([_ (in-range n)])
      (if (and rec? (pair? scope) (zero? (random 3)))
          (list-ref scope (random (length scope)))
          (random-shape (sub1 depth) #:allow-rec? allow-rec? scope))))
  (cond
    [(or (zero? depth) (zero? (random 3))) (term Int)]
    [else
     (define binder (string->symbol (format "X~a" depth)))
     (define inner (cons binder scope))
     (define left
       (for/list ([_ (in-range (random 3))])
         (random-shape (sub1 depth) #:allow-rec? allow-rec? scope)))
     (define right
       (for/list ([_ (in-range (random 3))])
         (if (and allow-rec? (zero? (random 2)))
             (list-ref inner (random (length inner)))
             (random-shape (sub1 depth) #:allow-rec? allow-rec? inner))))
     (term (Data ,binder ,left ,right))]))

;; The right constructor is taken less often as fuel runs out, and never once
;; it is gone, since only the right constructor may recur.
(define (random-value shape [fuel 4])
  (match shape
    ['Int (- (random 201) 100)]
    [`(Data ,_ ,_ ,_)
     (define side (if (or (zero? fuel) (zero? (random 2))) 'left 'right))
     (define payload
       (for/list ([field (in-list (term (data-fields ,shape ,side)))])
         (random-value field (sub1 (max 1 fuel)))))
     (if (eq? side 'left) (term (inl ,payload)) (term (inr ,payload)))]))

(define (random-tree fuel)
  (if (or (zero? fuel) (zero? (random 3)))
      (leaf (- (random 201) 100))
      (node (random-tree (sub1 fuel)) (random-tree (sub1 fuel)))))

;; A fresh-name supply for generated programs.
(define (name-supply prefix)
  (define counter (box 0))
  (lambda ()
    (set-box! counter (add1 (unbox counter)))
    (string->symbol (format "~a~a" prefix (unbox counter)))))

;; Emits the writes that lay `value` down through `writer`, then continues.
(define (write-value-term value writer next! k)
  (define (build value current k)
    (match value
      [(? integer? n)
       (define after (next!))
       (term (let (bind () (,after)) (write-int ,current ,n) ,(k after)))]
      [`(inl ,payload)
       (define tagged (next!))
       (term (let (bind () (,tagged)) (write-left ,current)
               ,(build-fields payload tagged k)))]
      [`(inr ,payload)
       (define tagged (next!))
       (term (let (bind () (,tagged)) (write-right ,current)
               ,(build-fields payload tagged k)))]))
  ;; A constructor's fields are written one after another, each from the
  ;; writer the previous one left.
  (define (build-fields values current k)
    (match values
      ['() (k current)]
      [(cons value rest)
       (build value current (lambda (middle) (build-fields rest middle k)))]))
  (build value writer k))

;; Emits a shape-directed copy from `reader` to `writer`.  Only for shapes
;; without recursion, because copying a recursive shape needs a recursive
;; function; that case is covered by `add1-tree` below.
(define (copy-term shape reader writer next-r! next-w! k)
  (define (copy shape rd wt k)
    (match shape
      ;; The integer goes through `if` and `arith` on its way to the writer:
      ;; both branches compute the value itself, so the copy is still exact,
      ;; and the `let` keeps the continuation out of the branches.
      ['Int
       (define value (next-r!))
       (define copied (next-r!))
       (define rd2 (next-r!))
       (define wt2 (next-w!))
       (term (let (bind (,value) (,rd2)) (read-int ,rd)
               (let (bind (,copied) ()) (if lt ,value 0
                                            (arith mul ,value 1)
                                            (arith sub ,value 0))
                 (let (bind () (,wt2)) (write-int ,wt ,copied)
                   ,(k rd2 wt2)))))]
      [`(Data ,_ ,_ ,_)
       (define rdl (next-r!)) (define wtl (next-w!))
       (define rdr (next-r!)) (define wtr (next-w!))
       (define lhs (term (data-fields ,shape left)))
       (define rhs (term (data-fields ,shape right)))
       (term (switch ,rd
              (left ,rdl (let (bind () (,wtl)) (write-left ,wt)
                           ,(copy-fields lhs rdl wtl k)))
              (right ,rdr (let (bind () (,wtr)) (write-right ,wt)
                            ,(copy-fields rhs rdr wtr k)))))]))
  (define (copy-fields shapes rd wt k)
    (match shapes
      ['() (k rd wt)]
      [(cons shape rest)
       (copy shape rd wt (lambda (rd2 wt2) (copy-fields rest rd2 wt2 k)))]))
  (copy shape reader writer k))

;; A closed program that writes `value`, reads it back, copies it into a fresh
;; writer, and finishes.  It should produce exactly the serialization of
;; `value`, and it exercises a reader and a writer that are live at the same
;; time -- which is where the affine/linear discipline actually bites.
(define (copy-program shape value)
  (define next-w! (name-supply 'w))
  (define next-r! (name-supply 'q))
  (define start (next-w!))
  (define body
    (write-value-term
     value start next-w!
     (lambda (final)
       (define out (next-w!))
       (term (let (bind (s) ()) (finish ,final)
               (let (bind () (rd0)) (open s)
                 (let (bind () (,out)) (new ,shape)
                   ,(copy-term shape 'rd0 out next-r! next-w!
                               (lambda (rd wt) (term (finish ,wt)))))))))))
  (term (let (bind () (,start)) (new ,shape) ,body)))

;; ---------------------------------------------------------------------------
;; Adequacy of the encoding
;;
;; Encoding and decoding are each partial functions, they are inverse, and a
;; value's cells are a prefix that decodes the same way whatever follows them.
;; That last part is what makes it safe for a cursor to sit in the middle of a
;; larger store.
;; ---------------------------------------------------------------------------

(define (check-layout-adequacy trials)
  (for ([_ (in-range trials)])
    (define shape (random-shape 4))
    (define value (random-value shape))
    (define cells (judgment-holds (serializes ,shape ,value S) S))
    ;; Encoding is a function.
    (check-equal? (length cells) 1)
    ;; Its result decodes back to exactly the value, with nothing left over.
    (check-equal? (judgment-holds (consumes ,shape ,(car cells) v ()) v)
                  (list value))
    ;; Decoding is a function too.
    (check-equal?
     (length (judgment-holds (consumes ,shape ,(car cells) v S) (v S)))
     1)
    ;; With unrelated cells appended, the value decodes the same way and the
    ;; extra cells come back unread.
    (check-equal?
     (judgment-holds (consumes ,shape ,(append (car cells) '(L (I 0))) v S) (v S))
     (list (list value '(L (I 0)))))))

;; ---------------------------------------------------------------------------
;; Taking a constructor keeps a protocol well formed
;;
;; The fields of a closed datatype are closed.  This is the one fact about
;; shapes the cursors need, and it is why no typing rule has to re-check the
;; protocol it advances to.
;; ---------------------------------------------------------------------------

(define (car-or-false t) (and (pair? t) (car t)))

(define (check-fields-closed trials)
  (for ([_ (in-range trials)])
    (define shape (random-shape 4))
    (check-true (judgment-holds (closed-shape-wf ,shape)))
    (when (eq? (car-or-false shape) (quote Data))
      (check-true (judgment-holds (protocol-wf (data-fields ,shape left))))
      (check-true (judgment-holds (protocol-wf (data-fields ,shape right)))))))

;; ---------------------------------------------------------------------------
;; Matching binds the frames correctly
;;
;; Two properties.  Matching a formal prefix against an actual protocol splits
;; the actual one into that prefix followed by the remainder; and
;; instantiating the formal row at the solution recovers the actual row.
;; Together they say a call site gets back exactly the cursor position it
;; would have had if the callee's traversal had been written out inline.
;; ---------------------------------------------------------------------------

;; If the formal prefix matches, the actual protocol is the formal prefix
;; followed by the remainder.
(define (match-prefix-splits formal actual)
  (define remainder (term (match-prefix ,formal ,actual)))
  (or (equal? remainder (term #f))
      (equal? actual (append formal remainder))))

;; Instantiating a formal input row at the frame matching bound for it
;; recovers the actual row exactly.  The formal is the first input, so its
;; frame, if it has one, is `(tvar 0)`.
(define (match-row-instantiates formal actual)
  (define bound (term (match-row ,formal ,actual)))
  (or (equal? bound (term #f))
      (not (member (term (row-tail ,formal)) (list 'closed '(tvar 0))))
      (equal? (term (instantiate-row (,bound) ,formal)) actual)))

;; Matching never looks past the part of the actual protocol it consumes, so
;; extending the actual protocol extends the remainder by the same cells.
;; That is what makes tail substitution work: instantiating a caller's frames
;; grows the actual rows at the end, and the solution grows in step, which is
;; why a signature body checked once against its declared rows serves every
;; call site.  (Rocq: `match_prefix_append`,
;; `match_resource_types_instantiate`.)
(define (match-prefix-extends formal actual suffix)
  (define remainder (term (match-prefix ,formal ,actual)))
  (or (equal? remainder (term #f))
      (equal? (term (match-prefix ,formal ,(append actual suffix)))
              (append remainder suffix))))

;; ---------------------------------------------------------------------------
;; Cursors stay canonical
;;
;; Opening a finished value gives a canonical reader, and every reader step
;; from a canonical reader lands on a canonical one.  A fresh writer is
;; canonical, every write keeps it canonical, and finishing one gives back a
;; canonical value.  These are the invariants the type system is trying to
;; maintain; checking them directly is how to tell whether it does.
;; ---------------------------------------------------------------------------

(define (check-capability-canonicity trials)
  (for ([_ (in-range trials)])
    (define shape (random-shape 3))
    (define value (random-value shape))
    (define cells (serialize shape value))
    (define serialized (term (ser ,shape ,cells)))
    (check-true (judgment-holds (serialization-canonical ,serialized)))

    ;; Opening a canonical serialization gives a canonical reader, and every
    ;; step from a canonical reader lands on a canonical reader.
    (let loop ([reader (term (open-serialization ,serialized))] [fuel 100])
      (check-true (judgment-holds (reader-canonical ,reader)))
      (define events (judgment-holds (reader-step ,reader ev) ev))
      ;; Reader stepping is deterministic.
      (check-equal? (length events) 1)
      (when (positive? fuel)
        (match (car events)
          ['r-done (void)]
          [`(r-int ,_ ,next) (loop next (sub1 fuel))]
          [`(r-left ,next) (loop next (sub1 fuel))]
          [`(r-right ,next) (loop next (sub1 fuel))])))

    ;; Replaying the same cells through a writer keeps it canonical, and the
    ;; serialization it finishes with is canonical.
    (let loop ([writer (term (new-writer ,shape))] [remaining cells])
      (check-true (judgment-holds (writer-canonical ,writer)))
      (cond
        [(null? remaining)
         (check-equal? (term (writer-finished ,writer)) (term #t))
         (define finished (term (finish-writer ,writer)))
         (check-true (judgment-holds (serialization-canonical ,finished)))
         (check-equal? finished serialized)]
        [else
         (check-equal? (term (writer-finished ,writer)) (term #f))
         (define next
           (match (car remaining)
             [`(I ,n) (term (writer-write-int ,writer ,n))]
             ['L (term (writer-write-left ,writer))]
             ['R (term (writer-write-right ,writer))]))
         (check-not-equal? next (term #f))
         (loop next (cdr remaining))]))))

;; ---------------------------------------------------------------------------
;; Type safety
;;
;; A closed, well-typed program never gets stuck: every state it passes
;; through is either final or can step.  Since the machine deliberately can
;; get stuck -- a linear scope frame refuses to pop while its writer is still
;; bound -- this says something.  Along the way, every state has at most one
;; successor, so the machine is deterministic.
;;
;; The programs checked are the worked examples, generated shape-directed copy
;; programs, and the recursive traversals on generated trees, each compared
;; against its ordinary meaning.
;;
;; This is the sampled form of Rocq's `type_safety`: every configuration
;; reachable from a closed well-typed program is final or steps.  There it is
;; a corollary of `typed_configuration_progress` and
;; `configuration_preservation` -- which is the point of stating it, since
;; those two are proved separately and only their composition says the
;; configuration typing is the right invariant.
;; ---------------------------------------------------------------------------

;; Runs `state`, checking at every step that it is either final or can step,
;; and that it can step in exactly one way.  Returns the final state.
(define (run-checking state [fuel 20000])
  (let loop ([current state] [fuel fuel])
    (define nexts (apply-reduction-relation machine-step current))
    (cond
      [(null? nexts)
       ;; Nowhere to go: for a well-typed program that has to mean final.
       (check-true (term (final? ,current))
                   (format "stuck at non-final configuration: ~e" current))
       current]
      [(zero? fuel) (error 'run-checking "out of fuel")]
      [else
       (check-equal? (length nexts) 1
                     (format "machine offered two steps at: ~e" current))
       (loop (car nexts) (sub1 fuel))])))

(define (check-type-safety sigma expression expected-result)
  (define types (type-of sigma expression))
  (check-equal? (length types) 1
                (format "expected exactly one typing for ~e, got ~e"
                        expression types))
  (define final (run-checking (term (initial ,sigma ,expression))))
  (check-equal? (result-of final) expected-result)
  (car types))

;; ---------------------------------------------------------------------------
;; The two candidates lay values out identically
;;
;; Packing a value as a span puts down the same cells the cursor core would
;; write, and the span it returns delimits exactly what a reader opened on
;; that value would have as its endpoint.  The candidates differ in access
;; discipline, not in representation.
;; ---------------------------------------------------------------------------

(define (check-span-agreement trials)
  (for ([_ (in-range trials)])
    (define shape (random-shape 4))
    (define value (random-value shape))
    (define cells (serialize shape value))
    (define packed
      (apply-reduction-relation span-reduction (term (() (pack ,shape ,value)))))
    (check-equal? (length packed) 1)
    (check-equal? (first (car packed)) cells)
    (define sp (second (car packed)))
    (check-true (judgment-holds (span-valid ,cells ,sp)))
    ;; The span's endpoint is where a reader's endpoint would be.
    (check-equal? sp (term (span ,shape 0 ,(length cells))))))

(module+ test
  (random-seed 20260829)

  ;; --- layout -------------------------------------------------------------
  (check-layout-adequacy 100)

  ;; --- shapes -------------------------------------------------------------
  (check-fields-closed 100)

  ;; --- tail matching ------------------------------------------------------
  (check-true
   (redex-check Match (P_1 P_2)
                (match-prefix-splits (term P_1) (term P_2))
                #:attempts 300
                #:print? #f))
  (check-true
   (redex-check Match (rho_1 rho_2)
                (match-row-instantiates (term rho_1) (term rho_2))
                #:attempts 300
                #:print? #f))
  (check-true
   (redex-check Match (P_1 P_2 P_3)
                (match-prefix-extends (term P_1) (term P_2) (term P_3))
                #:attempts 300
                #:print? #f))
  ;; Sampling the grammar rarely produces a pair that matches at all, so the
  ;; properties above would pass without exercising the matcher.  Drive it as
  ;; well with rows built from a shared prefix, where matching must succeed.
  (for ([_ (in-range 200)])
    (define prefix (for/list ([_ (in-range (random 3))]) (random-shape 2)))
    (define suffix (for/list ([_ (in-range (random 3))]) (random-shape 2)))
    (define formal (term (row ,prefix (tvar 0))))
    (define actual (term (row ,(append prefix suffix) closed)))
    (check-not-equal? (term (match-row ,formal ,actual)) (term #f))
    (check-true (match-row-instantiates formal actual))
    ;; Extending the actual protocol extends the remainder by the same cells.
    (check-true (match-prefix-extends prefix (append prefix suffix)
                                      (list (random-shape 2)))))

  ;; --- capabilities -------------------------------------------------------
  (check-capability-canonicity 40)

  ;; --- type safety on the worked examples ---------------------------------
  (void (check-type-safety (term ()) build-seven (term (ser Int ((I 7))))))

  ;; --- type safety on generated copy programs -----------------------------
  (for ([_ (in-range 25)])
    (define shape (random-shape 3 #:allow-rec? #f))
    (define value (random-value shape))
    (void (check-type-safety (term ()) (copy-program shape value)
                             (term (ser ,shape ,(serialize shape value))))))

  ;; --- type safety on the recursive traversals ----------------------------
  (for ([_ (in-range 10)])
    (define tree (random-tree 3))
    (void (check-type-safety recursive-signatures (sum-tree-program tree)
                             (tree-sum tree)))
    (void (check-type-safety recursive-signatures (add1-tree-program tree)
                             (term (ser ,tree-shape
                                        ,(serialize tree-shape
                                                    (tree-add1 tree))))))
    (void (check-type-safety recursive-signatures (mirror-tree-program tree)
                             (term (ser ,tree-shape
                                        ,(serialize tree-shape
                                                    (tree-mirror tree)))))))

  ;; --- cross-model agreement ----------------------------------------------
  (check-span-agreement 60))
