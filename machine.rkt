#lang racket

;; The abstract machine.
;;
;; A configuration is a control, an ordinary environment, a resource
;; environment, and a stack of frames.  Evaluation is environment-based rather
;; than substitution-based because the resource environment *is* the
;; substructural state: a cursor exists exactly as long as it has a binding,
;; and advancing one removes the old binding in the same step that adds the
;; new.  Nothing can hold a stale cursor, because a stale cursor has no name.
;;
;; Every term runs to a *bundle*: ordinary values and capabilities.  There are
;; three frames:
;;
;;   - `(frame-let (bind (x ...) (r ...)) e E)` waits for the right-hand side
;;     of a `let`, then binds what it produced and runs the body;
;;   - `(frame-scope E (r ...))` closes the scope of the names a `let` or a
;;     `switch` bound.  A reader still bound is dropped: abandoning one is
;;     legal.  A writer still bound makes the machine stuck: abandoning one is
;;     not legal, and the machine refuses rather than producing a truncated
;;     value;
;;   - `(frame-call E D)` holds a caller's environments while the callee
;;     runs.  Returning throws away the callee's environment, so it checks
;;     that the callee is not still holding a writer.
;;
;; Those checks are deliberately in the machine even though the type system
;; already rules them out.  Being able to get stuck is what makes "a
;; well-typed program never gets stuck" say something.
;;
;; Since binders are named, a rule that binds a name renames it to one fresh
;; for the whole state, and the environment records that fresh name.
;;
;; The signature environment sits beside the configuration rather than inside
;; it, so a configuration is exactly the runtime state and nothing else.
;;
;; See explore.rkt for stepping and drawing runs of this relation.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "layout.rkt"
         "protocol.rkt"
         "capability.rkt"
         "syntax.rkt"
         "match.rkt"
         "typing.rkt")

(provide (all-defined-out))

(define-extended-language Machine Typing
  ;; An ordinary value is an integer or a finished serialization.
  (rv ::= n sz)
  (rv? ::= rv #f)
  ;; A capability is a reader or a writer.
  (rr ::= rd wr)
  (rr? ::= rr #f)
  (E ::= ((x rv) ...))
  (D ::= ((r rr) ...))
  (rvs? ::= (rv ...) #f)
  ;; The capabilities pulled out of an environment, and what was left.
  (tr ::= ((rr ...) D))
  (tr? ::= tr #f)

  (F ::= (frame-let (bind (x ...) (r ...)) e E)
         (frame-scope E (r ...))
         (frame-call E D))
  (K ::= (F ...))

  (ctl ::= (ctl-term e) result)
  (result ::= (ctl-bundle (rv ...) (rr ...)))

  ;; The nonterminal is `cfg` because Redex reads a leading `config` inside a
  ;; production as a reference to the nonterminal of that name.
  (cfg ::= (config ctl E D K))
  (st ::= (machine Sigma cfg)))

;; ---------------------------------------------------------------------------
;; Environments
;; ---------------------------------------------------------------------------

(define-metafunction Machine
  lookup-value : E x -> rv?
  [(lookup-value () x) #f]
  [(lookup-value ((x rv) (x_rest rv_rest) ...) x) rv]
  [(lookup-value ((x_1 rv_1) (x_rest rv_rest) ...) x)
   (lookup-value ((x_rest rv_rest) ...) x)])

(define-metafunction Machine
  eval-atom : E atom -> rv?
  [(eval-atom E n) n]
  [(eval-atom E x) (lookup-value E x)])

(define-metafunction Machine
  eval-atoms : E (atom ...) -> rvs?
  [(eval-atoms E ()) ()]
  [(eval-atoms E (atom atom_rest ...))
   (rv rv_rest ...)
   (where rv (eval-atom E atom))
   (where (rv_rest ...) (eval-atoms E (atom_rest ...)))]
  [(eval-atoms E (atom ...)) #f])

(define-metafunction Machine
  lookup-rr : D r -> rr?
  [(lookup-rr () r) #f]
  [(lookup-rr ((r rr) (r_rest rr_rest) ...) r) rr]
  [(lookup-rr ((r_1 rr_1) (r_rest rr_rest) ...) r)
   (lookup-rr ((r_rest rr_rest) ...) r)])

(define-metafunction Machine
  remove-rr : D r -> D
  [(remove-rr () r) ()]
  [(remove-rr ((r rr) (r_rest rr_rest) ...) r) ((r_rest rr_rest) ...)]
  [(remove-rr ((r_1 rr_1) (r_rest rr_rest) ...) r)
   ((r_1 rr_1) (r_2 rr_2) ...)
   (where ((r_2 rr_2) ...) (remove-rr ((r_rest rr_rest) ...) r))])

(define-metafunction Machine
  remove-rrs : D (r ...) -> D
  [(remove-rrs D ()) D]
  [(remove-rrs D (r r_rest ...)) (remove-rrs (remove-rr D r) (r_rest ...))])

;; Handing capabilities to a callee removes each one from the caller's
;; environment as it is collected, so nothing can be passed twice.
(define-metafunction Machine
  transfer : D (r ...) -> tr?
  [(transfer D ()) (() D)]
  [(transfer D (r r_rest ...))
   ((rr rr_rest ...) D_out)
   (where rr (lookup-rr D r))
   (where ((rr_rest ...) D_out) (transfer (remove-rr D r) (r_rest ...)))]
  [(transfer D (r ...)) #f])

(define-metafunction Machine
  is-writer : rr -> boolean
  [(is-writer (writer S P A)) #t]
  [(is-writer rr) #f])

(define-metafunction Machine
  runtime-all-affine : D -> boolean
  [(runtime-all-affine ()) #t]
  [(runtime-all-affine ((r rr) (r_rest rr_rest) ...))
   (runtime-all-affine ((r_rest rr_rest) ...))
   (where #f (is-writer rr))]
  [(runtime-all-affine D) #f])

(define-metafunction Machine
  no-writer-among : D (r ...) -> boolean
  [(no-writer-among D ()) #t]
  [(no-writer-among D (r r_rest ...))
   (no-writer-among D (r_rest ...))
   (where #f (lookup-rr D r))]
  [(no-writer-among D (r r_rest ...))
   (no-writer-among D (r_rest ...))
   (where rr (lookup-rr D r))
   (where #f (is-writer rr))]
  [(no-writer-among D (r ...)) #f])

;; Names avoiding every symbol in the given term, which covers both the
;; environment domains and the free names of the body.
(define-metafunction Machine
  fresh-names : any (x ...) -> (x ...)
  [(fresh-names any (x ...)) ,(variables-not-in (term any) (term (x ...)))])

;; ---------------------------------------------------------------------------
;; Stepping
;; ---------------------------------------------------------------------------

(define machine-step
  (reduction-relation
   Machine
   #:domain st

   ;; --- terms -------------------------------------------------------------

   ;; Handing resources back removes each one from the environment, so
   ;; nothing can be handed back twice.
   (--> (machine Sigma (config (ctl-term (return (atom ...) (r ...))) E D K))
        (machine Sigma (config (ctl-bundle (rv ...) (rr ...)) E D_rest K))
        (where (rv ...) (eval-atoms E (atom ...)))
        (where ((rr ...) D_rest) (transfer D (r ...)))
        "return")

   (--> (machine Sigma (config (ctl-term (let (bind (x ...) (r ...)) e_rhs e_body))
                               E D (F ...)))
        (machine Sigma (config (ctl-term e_rhs) E D
                               ((frame-let (bind (x ...) (r ...)) e_body E) F ...)))
        "let")

   ;; No binder and no frame: the chosen branch simply replaces the term.
   (--> (machine Sigma (config (ctl-term (if cmp atom_lhs atom_rhs e_true e_false)) E D K))
        (machine Sigma (config (ctl-term e_true) E D K))
        (where n_lhs (eval-atom E atom_lhs))
        (where n_rhs (eval-atom E atom_rhs))
        (where #t (eval-compare cmp n_lhs n_rhs))
        "if-true")

   (--> (machine Sigma (config (ctl-term (if cmp atom_lhs atom_rhs e_true e_false)) E D K))
        (machine Sigma (config (ctl-term e_false) E D K))
        (where n_lhs (eval-atom E atom_lhs))
        (where n_rhs (eval-atom E atom_rhs))
        (where #f (eval-compare cmp n_lhs n_rhs))
        "if-false")

   ;; Which branch is taken is decided by the tag in the store, not by the
   ;; term: these two rules are disjoint because a reader steps one way only.
   ;; The source reader's binding goes away in the same step the successor's
   ;; appears; there is no state in which both exist.
   (--> (machine Sigma
                 (config (ctl-term (switch r_src (left r_lhs e_lhs)
                                                 (right r_rhs e_rhs)))
                         E D (F ...)))
        (machine Sigma (config (ctl-term e_scoped) E
                               ((r_fresh rd_next) (r_rest rr_rest) ...)
                               ((frame-scope E (r_fresh)) F ...)))
        (where rd_cur (lookup-rr D r_src))
        (judgment-holds (reader-step rd_cur (r-left rd_next)))
        (where ((r_rest rr_rest) ...) (remove-rr D r_src))
        (fresh (r_fresh r_lhs))
        (where e_scoped (rename-resource e_lhs r_lhs r_fresh))
        "switch-left")

   (--> (machine Sigma
                 (config (ctl-term (switch r_src (left r_lhs e_lhs)
                                                 (right r_rhs e_rhs)))
                         E D (F ...)))
        (machine Sigma (config (ctl-term e_scoped) E
                               ((r_fresh rd_next) (r_rest rr_rest) ...)
                               ((frame-scope E (r_fresh)) F ...)))
        (where rd_cur (lookup-rr D r_src))
        (judgment-holds (reader-step rd_cur (r-right rd_next)))
        (where ((r_rest rr_rest) ...) (remove-rr D r_src))
        (fresh (r_fresh r_rhs))
        (where e_scoped (rename-resource e_rhs r_rhs r_fresh))
        "switch-right")

   (--> (machine Sigma (config (ctl-term (arith aop atom_lhs atom_rhs)) E D K))
        (machine Sigma (config (ctl-bundle (n_out) ()) E D K))
        (where n_lhs (eval-atom E atom_lhs))
        (where n_rhs (eval-atom E atom_rhs))
        (where n_out (eval-arith aop n_lhs n_rhs))
        "arith")

   ;; Each cursor step consumes the cursor and produces its successor.
   (--> (machine Sigma (config (ctl-term (read-int r)) E D K))
        (machine Sigma (config (ctl-bundle (n) (rd_next)) E (remove-rr D r) K))
        (where rd_cur (lookup-rr D r))
        (judgment-holds (reader-step rd_cur (r-int n rd_next)))
        "read-int")

   (--> (machine Sigma (config (ctl-term (write-int r atom)) E D K))
        (machine Sigma (config (ctl-bundle () (wr_next)) E (remove-rr D r) K))
        (where wr_cur (lookup-rr D r))
        (where n (eval-atom E atom))
        (where wr_next (writer-write-int wr_cur n))
        "write-int")

   (--> (machine Sigma (config (ctl-term (write-left r)) E D K))
        (machine Sigma (config (ctl-bundle () (wr_next)) E (remove-rr D r) K))
        (where wr_cur (lookup-rr D r))
        (where wr_next (writer-write-left wr_cur))
        "write-left")

   (--> (machine Sigma (config (ctl-term (write-right r)) E D K))
        (machine Sigma (config (ctl-bundle () (wr_next)) E (remove-rr D r) K))
        (where wr_cur (lookup-rr D r))
        (where wr_next (writer-write-right wr_cur))
        "write-right")

   (--> (machine Sigma (config (ctl-term (open atom)) E D K))
        (machine Sigma (config (ctl-bundle () ((open-serialization sz))) E D K))
        (where sz (eval-atom E atom))
        "open")

   (--> (machine Sigma (config (ctl-term (new A)) E D K))
        (machine Sigma (config (ctl-bundle () ((new-writer A))) E D K))
        "new")

   (--> (machine Sigma (config (ctl-term (finish r)) E D K))
        (machine Sigma (config (ctl-bundle (sz) ()) E (remove-rr D r) K))
        (where wr_cur (lookup-rr D r))
        (where #t (writer-finished wr_cur))
        (where sz (finish-writer wr_cur))
        "finish")

   ;; The callee runs in a fresh environment holding only what it was given.
   ;; The caller's environments wait on the frame.
   (--> (machine Sigma (config (ctl-term (call f (atom ...) (r_arg ...))) E D (F ...)))
        (machine Sigma (config (ctl-term e_body)
                               ((x_param rv) ...)
                               ((r_param rr) ...)
                               ((frame-call E D_rest) F ...)))
        (where df (lookup-signature f Sigma))
        (where (rv ...) (eval-atoms E (atom ...)))
        (where ((rr ...) D_rest) (transfer D (r_arg ...)))
        (where (bind (x_formal ...) (r_formal ...)) (parameters-of df))
        (side-condition (= (length (term (x_formal ...))) (length (term (rv ...)))))
        (side-condition (= (length (term (r_formal ...))) (length (term (rr ...)))))
        ;; The parameters are renamed inside the callee's body, so the new
        ;; names must avoid that body and the other formals too.
        (where e_callee (body-of df))
        (where (x_param ...)
               (fresh-names (E D e_callee (x_formal ...) (r_formal ...))
                            (x_formal ...)))
        (where (r_param ...)
               (fresh-names (E D e_callee (x_formal ...) (r_formal ...))
                            (r_formal ...)))
        (where e_body (open-let-body e_callee
                                     (x_formal ...) (x_param ...)
                                     (r_formal ...) (r_param ...)))
        "call")

   ;; --- results ------------------------------------------------------------

   ;; The let's environments are extended with what the right-hand side
   ;; produced, under fresh names, and a scope frame waits to close them.
   (--> (machine Sigma
                 (config (ctl-bundle (rv ...) (rr ...)) E D
                         ((frame-let (bind (x_bind ...) (r_bind ...)) e E_outer)
                          F ...)))
        (machine Sigma (config (ctl-term e_scoped)
                               ((x_fresh rv) ... (x_outer rv_outer) ...)
                               ((r_fresh rr) ... (r_env rr_env) ...)
                               ((frame-scope E_outer (r_fresh ...)) F ...)))
        (side-condition (= (length (term (x_bind ...))) (length (term (rv ...)))))
        (side-condition (= (length (term (r_bind ...))) (length (term (rr ...)))))
        (where ((x_outer rv_outer) ...) E_outer)
        (where ((r_env rr_env) ...) D)
        (where (x_fresh ...) (fresh-names (E_outer D e) (x_bind ...)))
        (where (r_fresh ...) (fresh-names (E_outer D e) (r_bind ...)))
        (where e_scoped (open-let-body e (x_bind ...) (x_fresh ...)
                                         (r_bind ...) (r_fresh ...)))
        "let-continue")

   ;; A reader may still be bound; drop it.  A writer must already be gone,
   ;; or there is no step from here.
   (--> (machine Sigma (config result E D ((frame-scope E_outer (r ...)) F ...)))
        (machine Sigma (config result E_outer (remove-rrs D (r ...)) (F ...)))
        (where #t (no-writer-among D (r ...)))
        "scope")

   ;; Returning from a call discards whatever the callee still holds, so it
   ;; must not hold a writer.  The caller's environments come back off the
   ;; frame, and the result goes on to the caller's next frame.
   (--> (machine Sigma (config result E D ((frame-call E_caller D_caller) F ...)))
        (machine Sigma (config result E_caller D_caller (F ...)))
        (where #t (runtime-all-affine D))
        "call-return")))

;; ---------------------------------------------------------------------------
;; Running
;; ---------------------------------------------------------------------------

(define-metafunction Machine
  initial : Sigma e -> st
  [(initial Sigma e) (machine Sigma (config (ctl-term e) () () ()))])

;; A state is final when it has an answer and an empty stack.  A state that is
;; neither final nor able to step is stuck.
(define-metafunction Machine
  final? : st -> boolean
  [(final? (machine Sigma (config result E D ()))) #t]
  [(final? st) #f])

;; Steps to a normal form, which may be final or stuck.  Raises if the machine
;; ever offers two steps, since that would mean it is not deterministic.
(define (run state #:fuel [fuel 10000])
  (let loop ([current state] [remaining fuel])
    (define nexts (apply-reduction-relation machine-step current))
    (cond
      [(null? nexts) current]
      [(zero? remaining) (error 'run "out of fuel at ~e" current)]
      [(null? (cdr nexts)) (loop (car nexts) (sub1 remaining))]
      [else (error 'run "machine offered two steps: ~e" nexts)])))

(define (run-term sigma expression #:fuel [fuel 10000])
  (run (term (initial ,sigma ,expression)) #:fuel fuel))

;; The answer of a finished run, or `#f` if it got stuck.
(define (result-of state)
  (match state
    [`(machine ,_ (config (ctl-bundle (,value) ()) ,_ ,_ ())) value]
    [`(machine ,_ (config (ctl-bundle ,values ,resources) ,_ ,_ ()))
     (list values resources)]
    [_ #f]))

(module+ test
  (define build-seven
    (term (let (bind () (w)) (new Int)
            (let (bind () (w2)) (write-int w 7)
              (finish w2)))))
  (check-equal? (result-of (run-term (term ()) build-seven))
                (term (ser Int ((I 7)))))
  (check-true (term (final? ,(run-term (term ()) build-seven))))

  ;; Write 7, open the result, read it back.
  (check-equal?
   (result-of
    (run-term (term ())
              (term (let (bind (s) ()) ,build-seven
                      (let (bind () (rd)) (open s)
                        (let (bind (v) (rd2)) (read-int rd)
                          (return (v) ())))))))
   7)

  ;; The tag in the store, not the term, picks the branch.
  (check-equal?
   (result-of
    (run-term (term ())
              (term (let (bind (s) ())
                         (let (bind () (w)) (new (Data X (Int) (Int)))
                           (let (bind () (w2)) (write-right w)
                             (let (bind () (w3)) (write-int w2 5)
                               (finish w3))))
                      (let (bind () (rd)) (open s)
                        (switch rd
                          (left rd1 (let (bind (v) (rd2)) (read-int rd1)
                                      (return (0) ())))
                          (right rd1 (let (bind (v) (rd2)) (read-int rd1)
                                       (return (v) ())))))))))
   5)

  (check-equal?
   (result-of (run-term (term ()) (term (arith add 2 3))))
   5)
  (check-equal?
   (result-of
    (run-term (term ()) (term (let (bind (a) ()) (arith sub 2 3)
                                (arith mul a 10)))))
   -10)
  (check-equal?
   (result-of (run-term (term ()) (term (if lt 2 3 (return (1) ()) (return (0) ())))))
   1)
  (check-equal?
   (result-of (run-term (term ()) (term (if eq 2 3 (return (1) ()) (return (0) ())))))
   0)

  ;; Writing past the protocol gets stuck rather than producing garbage.
  (check-false
   (result-of
    (run-term (term ())
              (term (let (bind () (w)) (new Int)
                      (let (bind () (w2)) (write-int w 7)
                        (let (bind () (w3)) (write-int w2 8)
                          (finish w3))))))))

  ;; Abandoning a writer gets stuck at its scope frame.
  (check-false
   (result-of (run-term (term ()) (term (let (bind () (w)) (new Int)
                                          (return (1) ()))))))
  ;; Abandoning a reader does not.
  (check-equal?
   (result-of
    (run-term (term ())
              (term (let (bind (s) ()) ,build-seven
                      (let (bind () (rd)) (open s)
                        (return (1) ()))))))
   1)

  ;; Every reachable state offers at most one step.
  (define (deterministic-run? state)
    (let loop ([current state] [fuel 1000])
      (define nexts (apply-reduction-relation machine-step current))
      (cond [(null? nexts) #t]
            [(zero? fuel) #f]
            [(pair? (cdr nexts)) #f]
            [else (loop (car nexts) (sub1 fuel))])))
  (check-true (deterministic-run? (term (initial () ,build-seven))))

  ;; A call renames the callee's parameters apart from the callee's own
  ;; binders.  Here the callee's body binds `n1` and hands back `n`, so the
  ;; formal `n` has to be renamed to something other than `n1`, or the call
  ;; would return 6.
  (define capture-sigma
    (term ((f (def (sig (Int) () (Int) ()) (bind (n) ())
                (let (bind (n1) ()) (arith add n 1)
                  (return (n) ())))))))
  (check-equal?
   (result-of
    (run-term capture-sigma
              (term (let (bind (y) ()) (call f (5) ())
                      (arith add y 0)))))
   5))
