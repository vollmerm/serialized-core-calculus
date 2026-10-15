#lang racket

;; Cursors: the capabilities that read and write serialized data in place.
;;
;; A *reader* is positioned somewhere in a store, owes a protocol, and knows
;; where the value it was opened on ends.  Reading is destructive on the
;; capability, not on the data: each step consumes the reader and hands back a
;; successor positioned one cell further along.  Readers are affine -- a
;; program may abandon one -- so a traversal that ignores a subtree is fine.
;;
;; A *writer* holds the cells appended so far, the protocol it still owes, and
;; the shape it is building.  It is linear: every writer must be either
;; advanced or finished, because abandoning one halfway would leave a
;; half-built value in the buffer with nothing to say how long it is.
;;
;; The endpoint a reader carries is what makes `r-done` meaningful.  With no
;; terminator in the encoding, "I have read everything I was given" can only
;; be stated as "my protocol is exhausted *and* I am standing exactly where my
;; value ended".  A reader whose protocol runs out early is stuck, not done.
;;
;; The canonical-form judgments at the bottom are the invariants that make
;; those claims true: a canonical reader's remaining protocol is exactly
;; satisfiable by the cells in front of it, and a canonical writer's cells are
;; exactly what replaying its actions from a fresh buffer would have produced.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "layout.rkt"
         "protocol.rkt")

(provide (all-defined-out))

(define-extended-language Capability Protocol
  ;; A finished value: its shape and its cells.
  (sz ::= (ser A S))
  ;; store, pending protocol, position, endpoint
  (rd ::= (reader S P natural natural))
  ;; cells written so far, pending protocol, result shape
  (wr ::= (writer S P A))
  (wr? ::= wr #f)
  ;; What a reader step reveals, together with the successor reader.
  (ev ::= (r-int n rd) (r-left rd) (r-right rd) r-done))

(define-metafunction Capability
  store-ref : S natural -> cell or #f
  [(store-ref (cell_0 cell_rest ...) 0) cell_0]
  [(store-ref (cell_0 cell_rest ...) natural)
   (store-ref (cell_rest ...) ,(sub1 (term natural)))]
  [(store-ref () natural) #f])

(define-metafunction Capability
  store-drop : S natural -> S
  [(store-drop S 0) S]
  [(store-drop (cell_0 cell_rest ...) natural)
   (store-drop (cell_rest ...) ,(sub1 (term natural)))]
  [(store-drop () natural) ()])

;; ---------------------------------------------------------------------------
;; Reading
;;
;; A reader with no step available is stuck.  There is no error result to
;; propagate: absence of a derivation is the whole story, which is what makes
;; "a well-typed reader is never stuck" a statement worth checking.
;; ---------------------------------------------------------------------------

(define-judgment-form Capability
  #:mode (reader-step I O)
  #:contract (reader-step rd ev)

  ;; Finished: nothing owed, and standing exactly on the endpoint.  The
  ;; repeated `natural` is the equality check.
  [------------------------------ "done"
   (reader-step (reader S () natural natural) r-done)]

  [(where (I n) (store-ref S natural_pos))
   (where natural_next ,(add1 (term natural_pos)))
   ------------------------------ "integer"
   (reader-step (reader S (Int A_tail ...) natural_pos natural_end)
                (r-int n (reader S (A_tail ...) natural_next natural_end)))]

  ;; The tag chooses which constructor's fields are owed next; the rest of
  ;; the protocol is untouched.
  [(where L (store-ref S natural_pos))
   (where natural_next ,(add1 (term natural_pos)))
   (where (A_field ...) (data-fields A left))
   ------------------------------ "left"
   (reader-step (reader S ((name A (Data X P_left P_right)) A_tail ...)
                        natural_pos natural_end)
                (r-left (reader S (A_field ... A_tail ...) natural_next natural_end)))]

  [(where R (store-ref S natural_pos))
   (where natural_next ,(add1 (term natural_pos)))
   (where (A_field ...) (data-fields A right))
   ------------------------------ "right"
   (reader-step (reader S ((name A (Data X P_left P_right)) A_tail ...)
                        natural_pos natural_end)
                (r-right (reader S (A_field ... A_tail ...) natural_next natural_end)))])

;; Opening a finished value: a reader at the start, owing that one shape, with
;; the endpoint at the end of its cells.
(define-metafunction Capability
  open-serialization : sz -> rd
  [(open-serialization (ser A (cell ...)))
   (reader (cell ...) (A) 0 ,(length (term (cell ...))))])

;; ---------------------------------------------------------------------------
;; Writing
;;
;; The protocol says which cell may be appended next; anything else is `#f`.
;; ---------------------------------------------------------------------------

(define-metafunction Capability
  new-writer : A -> wr
  [(new-writer A) (writer () (A) A)])

(define-metafunction Capability
  writer-write-int : wr n -> wr?
  [(writer-write-int (writer (cell ...) (Int A_tail ...) A) n)
   (writer (cell ... (I n)) (A_tail ...) A)]
  [(writer-write-int wr n) #f])

(define-metafunction Capability
  writer-write-left : wr -> wr?
  [(writer-write-left (writer (cell ...) ((name A_head (Data X P_left P_right)) A_tail ...) A))
   (writer (cell ... L) (A_field ... A_tail ...) A)
   (where (A_field ...) (data-fields A_head left))]
  [(writer-write-left wr) #f])

(define-metafunction Capability
  writer-write-right : wr -> wr?
  [(writer-write-right (writer (cell ...) ((name A_head (Data X P_left P_right)) A_tail ...) A))
   (writer (cell ... R) (A_field ... A_tail ...) A)
   (where (A_field ...) (data-fields A_head right))]
  [(writer-write-right wr) #f])

(define-metafunction Capability
  writer-finished : wr -> boolean
  [(writer-finished (writer S () A)) #t]
  [(writer-finished wr) #f])

(define-metafunction Capability
  finish-writer : wr -> sz
  [(finish-writer (writer S P A)) (ser A S)])

;; ---------------------------------------------------------------------------
;; Canonical forms
;;
;; These are the runtime invariants.  Nothing in the machine checks them; they
;; are what a well-typed program is supposed to maintain, and what the
;; property suite samples.
;; ---------------------------------------------------------------------------

;; The cells decode at the shape, exactly, with nothing left over.
(define-judgment-form Capability
  #:mode (serialization-canonical I)
  #:contract (serialization-canonical sz)
  [(closed-shape-wf A)
   (consumes A S v ())
   ------------------------------ "canonical"
   (serialization-canonical (ser A S))])

;; Everything the reader still owes is satisfiable by the cells in front of
;; it, and its endpoint is where satisfying them lands.
(define-judgment-form Capability
  #:mode (reader-canonical I)
  #:contract (reader-canonical rd)
  [(protocol-wf P)
   (side-condition ,(<= (term natural_pos) (length (term S))))
   (consumes-protocol P (store-drop S natural_pos) S_remaining)
   (side-condition
    ,(= (term natural_end)
        (- (length (term S)) (length (term S_remaining)))))
   ------------------------------ "canonical"
   (reader-canonical (reader S P natural_pos natural_end))])

;; The cells and the pending protocol are jointly reachable by writing from a
;; fresh buffer.  Read backwards from the last cell, this is a walk back to
;; `new-writer`.
(define-judgment-form Capability
  #:mode (writer-reachable I I O)
  #:contract (writer-reachable A S P)

  [(closed-shape-wf A)
   ------------------------------ "start"
   (writer-reachable A () (A))]

  [(writer-reachable A (cell ...) (Int A_tail ...))
   ------------------------------ "int"
   (writer-reachable A (cell ... (I n)) (A_tail ...))]

  [(writer-reachable A (cell ...) ((name A_head (Data X P_left P_right)) A_tail ...))
   (where (A_field ...) (data-fields A_head left))
   ------------------------------ "left"
   (writer-reachable A (cell ... L) (A_field ... A_tail ...))]

  [(writer-reachable A (cell ...) ((name A_head (Data X P_left P_right)) A_tail ...))
   (where (A_field ...) (data-fields A_head right))
   ------------------------------ "right"
   (writer-reachable A (cell ... R) (A_field ... A_tail ...))])

(define-judgment-form Capability
  #:mode (writer-canonical I)
  #:contract (writer-canonical wr)
  [(closed-shape-wf A)
   (protocol-wf P)
   (writer-reachable A S P)
   ------------------------------ "canonical"
   (writer-canonical (writer S P A))])

(module+ test
  (define sample-tree
    (term (inr ((inl (1)) (inl (2))))))
  (define sample-store (serialize tree-shape sample-tree))

  ;; Walking the running example, tag by tag.
  (define root (term (open-serialization (ser ,tree-shape ,sample-store))))
  (check-equal? root (term (reader (R L (I 1) L (I 2)) (,tree-shape) 0 5)))
  (check-true (judgment-holds (reader-canonical ,root)))

  (define node
    (car (judgment-holds (reader-step ,root (r-right rd)) rd)))
  (check-true (judgment-holds (reader-canonical ,node)))
  ;; After the node tag, two subtrees are owed.
  (check-equal? node (term (reader (R L (I 1) L (I 2))
                                   (,tree-shape ,tree-shape) 1 5)))

  ;; The left subtree's reader still owes the right one -- that is how the
  ;; traversal knows where to go next without any stored offset.
  (define leaf
    (car (judgment-holds (reader-step ,node (r-left rd)) rd)))
  (check-equal? leaf (term (reader (R L (I 1) L (I 2))
                                   (Int ,tree-shape) 2 5)))
  (check-equal? (judgment-holds (reader-step ,leaf (r-int n rd)) n)
                (list 1))

  ;; Reading is deterministic.
  (check-equal? (length (judgment-holds (reader-step ,root ev) ev)) 1)

  ;; Exhausted but not at the endpoint: stuck, not done.
  (check-false (judgment-holds (reader-step (reader ((I 1) (I 2)) () 0 2) ev)))
  (check-true (judgment-holds (reader-step (reader ((I 1)) () 1 1) r-done)))

  ;; Writers append exactly the cell the protocol calls for.
  (define w0 (term (new-writer (Data X (Int) (Int)))))
  (check-equal? (term (writer-write-int ,w0 9)) (term #f))
  (define w1 (term (writer-write-right ,w0)))
  (check-equal? w1 (term (writer (R) (Int) (Data X (Int) (Int)))))
  (define w2 (term (writer-write-int ,w1 9)))
  (check-equal? (term (writer-finished ,w1)) (term #f))
  (check-equal? (term (writer-finished ,w2)) (term #t))
  (check-equal? (term (finish-writer ,w2)) (term (ser (Data X (Int) (Int)) (R (I 9)))))
  (check-true (judgment-holds (writer-canonical ,w2)))
  (check-true
   (judgment-holds (serialization-canonical (ser (Data X (Int) (Int)) (R (I 9))))))

  ;; Cells that do not decode at the result shape are not canonical, and no
  ;; sequence of writes reaches them.
  (check-false
   (judgment-holds (serialization-canonical (ser (Data X (Int) (Int)) ((I 9))))))
  (check-false
   (judgment-holds (writer-canonical (writer ((I 9)) () (Data X (Int) (Int)))))))
