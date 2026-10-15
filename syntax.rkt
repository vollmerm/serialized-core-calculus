#lang racket

;; Terms, types, and function signatures.
;;
;; Every term produces a *bundle*: a list of ordinary values and a list of
;; resources.  The primitive operations are terms of their own -- `(write-int w
;; 7)` consumes the writer `w` and produces the successor writer -- and one
;; binder, `let`, names what a term produced: `(let (bind () (w2)) (write-int
;; w 7) e)` reads "write 7 through w, call the resulting writer w2, then do e".
;; The only other binder is `switch`, whose branches each name the reader they
;; continue with.  Consuming `w` removes it from scope, so the substructural
;; discipline is carried by the typing contexts rather than by a separate
;; effect system.
;;
;; There are three namespaces: ordinary variables `x` for integers,
;; serializations, and function results; resource variables `r` for cursors;
;; and function names `f`.  Redex draws all three from one pool of symbols, so
;; the renaming metafunctions below are split by namespace and never cross:
;; renaming an ordinary `a` leaves a resource binder named `a` untouched.
;;
;; A *signature* is what a recursive function declares: ordinary and resource
;; inputs and ordinary and resource outputs.  Resources are ordered lists
;; rather than a context because a call transfers exactly these capabilities
;; in and exactly those back out, positionally.  A resource input's row either
;; is closed or ends in `(tvar j)`, the frame of the input at position j,
;; standing for whatever the caller has after it; an output row may end in the
;; frame of any input.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "protocol.rkt"
         "capability.rkt")

(provide (all-defined-out))

(define-extended-language Syntax Capability
  (x ::= variable-not-otherwise-mentioned)
  (r ::= variable-not-otherwise-mentioned)
  (f ::= variable-not-otherwise-mentioned)

  (atom ::= n x)
  ;; Ordinary types: an integer, or a finished value of some shape.
  (T ::= Int (Ser A))
  ;; Resource types: a reader or a writer, each carrying the row it is
  ;; positioned at; a writer also carries the shape it is building.
  (R ::= (Read rho) (Write rho A))
  ;; What a term produces: ordinary values and an ordered list of resources.
  (res ::= (bundle (T ...) (R ...)))
  (mode ::= affine linear)
  ;; Integer arithmetic, and the comparisons `if` branches on.
  (aop ::= add sub mul)
  (cmp ::= eq lt le)

  (e ::=
     ;; return values and hand back resources
     (return (atom ...) (r ...))
     ;; let: run the first term, name what it produced, then run the second
     (let (bind (x ...) (r ...)) e e)
     ;; if: compare two integers; neither branch binds anything
     (if cmp atom atom e e)
     ;; switch: source reader; each branch binds its own successor
     (switch r (left r e) (right r e))
     (arith aop atom atom)
     (read-int r)
     (write-int r atom)
     (write-left r)
     (write-right r)
     ;; open a finished value for reading; new starts a writer for a shape
     (open atom)
     (new A)
     (finish r)
     ;; call: callee, ordinary arguments, resources handed over
     (call f (atom ...) (r ...)))

  ;; ordinary inputs, resource inputs, ordinary outputs, resource outputs
  (sg ::= (sig (T ...) (R ...) (T ...) (R ...)))
  (df ::= (def sg (bind (x ...) (r ...)) e))
  (Sigma ::= ((f df) ...)))

(define-metafunction Syntax
  eval-arith : aop n n -> n
  [(eval-arith add n_1 n_2) ,(+ (term n_1) (term n_2))]
  [(eval-arith sub n_1 n_2) ,(- (term n_1) (term n_2))]
  [(eval-arith mul n_1 n_2) ,(* (term n_1) (term n_2))])

(define-metafunction Syntax
  eval-compare : cmp n n -> boolean
  [(eval-compare eq n_1 n_2) ,(= (term n_1) (term n_2))]
  [(eval-compare lt n_1 n_2) ,(< (term n_1) (term n_2))]
  [(eval-compare le n_1 n_2) ,(<= (term n_1) (term n_2))])

(define-metafunction Syntax
  signature-of : df -> sg
  [(signature-of (def sg (bind (x ...) (r ...)) e)) sg])

(define-metafunction Syntax
  body-of : df -> e
  [(body-of (def sg (bind (x ...) (r ...)) e)) e])

(define-metafunction Syntax
  parameters-of : df -> (bind (x ...) (r ...))
  [(parameters-of (def sg (bind (x ...) (r ...)) e)) (bind (x ...) (r ...))])

(define-metafunction Syntax
  lookup-signature : f Sigma -> df or #f
  [(lookup-signature f ()) #f]
  [(lookup-signature f ((f df) (f_rest df_rest) ...)) df]
  [(lookup-signature f ((f_1 df_1) (f_rest df_rest) ...))
   (lookup-signature f ((f_rest df_rest) ...))])

(define-metafunction Syntax
  resource-type-row : R -> rho
  [(resource-type-row (Read rho)) rho]
  [(resource-type-row (Write rho A)) rho])

;; Readers are affine: abandoning one is fine.  Writers are linear: a
;; half-built value must not be abandoned.
(define-metafunction Syntax
  resource-mode : R -> mode
  [(resource-mode (Read rho)) affine]
  [(resource-mode (Write rho A)) linear])

;; ---------------------------------------------------------------------------
;; Renaming
;;
;; Opening a scope means renaming its binder to a chosen fresh name.  The
;; `-under` helpers stop the descent at a binder that rebinds the same name,
;; since occurrences below it belong to the inner binder.  Renaming is only
;; ever applied with a globally fresh target, so capture in the other
;; direction cannot arise.
;; ---------------------------------------------------------------------------

(define-metafunction Syntax
  rename-atom : atom x x -> atom
  [(rename-atom n x_old x_new) n]
  [(rename-atom x_old x_old x_new) x_new]
  [(rename-atom x x_old x_new) x])

;; Descend into a subterm unless the ordinary binder `x_bound` shadows.
(define-metafunction Syntax
  rename-ordinary : e x x -> e
  [(rename-ordinary (return (atom ...) (r ...)) x_old x_new)
   (return ((rename-atom atom x_old x_new) ...) (r ...))]

  ;; The bound names shadow inside the body only.
  [(rename-ordinary (let (bind (x_bv ...) (r_br ...)) e_rhs e_body) x_old x_new)
   (let (bind (x_bv ...) (r_br ...))
     (rename-ordinary e_rhs x_old x_new)
     ,(if (member (term x_old) (term (x_bv ...)))
          (term e_body)
          (term (rename-ordinary e_body x_old x_new))))]

  [(rename-ordinary (if cmp atom_1 atom_2 e_1 e_2) x_old x_new)
   (if cmp (rename-atom atom_1 x_old x_new) (rename-atom atom_2 x_old x_new)
       (rename-ordinary e_1 x_old x_new) (rename-ordinary e_2 x_old x_new))]

  [(rename-ordinary (switch r (left r_lhs e_lhs) (right r_rhs e_rhs))
                    x_old x_new)
   (switch r
           (left r_lhs (rename-ordinary e_lhs x_old x_new))
           (right r_rhs (rename-ordinary e_rhs x_old x_new)))]

  [(rename-ordinary (arith aop atom_1 atom_2) x_old x_new)
   (arith aop (rename-atom atom_1 x_old x_new) (rename-atom atom_2 x_old x_new))]
  [(rename-ordinary (write-int r atom) x_old x_new)
   (write-int r (rename-atom atom x_old x_new))]
  [(rename-ordinary (open atom) x_old x_new)
   (open (rename-atom atom x_old x_new))]
  [(rename-ordinary (call f (atom ...) (r ...)) x_old x_new)
   (call f ((rename-atom atom x_old x_new) ...) (r ...))]
  ;; The rest mention no ordinary variable.
  [(rename-ordinary e x_old x_new) e])

(define-metafunction Syntax
  rename-resource-var : r r r -> r
  [(rename-resource-var r_old r_old r_new) r_new]
  [(rename-resource-var r r_old r_new) r])

(define-metafunction Syntax
  rename-resource-under : e r r r -> e
  [(rename-resource-under e r_old r_old r_new) e]
  [(rename-resource-under e r_bound r_old r_new)
   (rename-resource e r_old r_new)])

(define-metafunction Syntax
  rename-resource : e r r -> e
  [(rename-resource (return (atom ...) (r_arg ...)) r_old r_new)
   (return (atom ...) ((rename-resource-var r_arg r_old r_new) ...))]

  [(rename-resource (let (bind (x_bv ...) (r_br ...)) e_rhs e_body) r_old r_new)
   (let (bind (x_bv ...) (r_br ...))
     (rename-resource e_rhs r_old r_new)
     ,(if (member (term r_old) (term (r_br ...)))
          (term e_body)
          (term (rename-resource e_body r_old r_new))))]

  [(rename-resource (if cmp atom_1 atom_2 e_1 e_2) r_old r_new)
   (if cmp atom_1 atom_2
       (rename-resource e_1 r_old r_new) (rename-resource e_2 r_old r_new))]

  [(rename-resource (switch r_src (left r_lhs e_lhs) (right r_rhs e_rhs))
                    r_old r_new)
   (switch (rename-resource-var r_src r_old r_new)
           (left r_lhs (rename-resource-under e_lhs r_lhs r_old r_new))
           (right r_rhs (rename-resource-under e_rhs r_rhs r_old r_new)))]

  [(rename-resource (read-int r) r_old r_new)
   (read-int (rename-resource-var r r_old r_new))]
  [(rename-resource (write-int r atom) r_old r_new)
   (write-int (rename-resource-var r r_old r_new) atom)]
  [(rename-resource (write-left r) r_old r_new)
   (write-left (rename-resource-var r r_old r_new))]
  [(rename-resource (write-right r) r_old r_new)
   (write-right (rename-resource-var r r_old r_new))]
  [(rename-resource (finish r) r_old r_new)
   (finish (rename-resource-var r r_old r_new))]
  [(rename-resource (call f (atom ...) (r_arg ...)) r_old r_new)
   (call f (atom ...) ((rename-resource-var r_arg r_old r_new) ...))]
  ;; The rest mention no resource variable.
  [(rename-resource e r_old r_new) e])

(define-metafunction Syntax
  rename-ordinary-many : e (x ...) (x ...) -> e
  [(rename-ordinary-many e () ()) e]
  [(rename-ordinary-many e (x_old x_olds ...) (x_new x_news ...))
   (rename-ordinary-many (rename-ordinary e x_old x_new)
                         (x_olds ...) (x_news ...))])

(define-metafunction Syntax
  rename-resource-many : e (r ...) (r ...) -> e
  [(rename-resource-many e () ()) e]
  [(rename-resource-many e (r_old r_olds ...) (r_new r_news ...))
   (rename-resource-many (rename-resource e r_old r_new)
                         (r_olds ...) (r_news ...))])

;; A let body is opened at two lists at once: the ordinary results and the
;; resources.
(define-metafunction Syntax
  open-let-body : e (x ...) (x ...) (r ...) (r ...) -> e
  [(open-let-body e (x_old ...) (x_new ...) (r_old ...) (r_new ...))
   (rename-resource-many
    (rename-ordinary-many e (x_old ...) (x_new ...))
    (r_old ...) (r_new ...))])

(module+ test
  ;; Renaming stops at a shadowing binder.
  (check-equal?
   (term (rename-ordinary (let (bind (a) ()) (arith add a 1) (return (a) ())) a z))
   (term (let (bind (a) ()) (arith add z 1) (return (a) ()))))
  (check-equal?
   (term (rename-ordinary (let (bind (b) ()) (arith add a 1) (return (a) ())) a z))
   (term (let (bind (b) ()) (arith add z 1) (return (z) ()))))
  ;; `if` binds nothing, so renaming reaches both branches.
  (check-equal?
   (term (rename-ordinary (if lt a 0 (return (a) ()) (return (b) ())) a z))
   (term (if lt z 0 (return (z) ()) (return (b) ()))))

  ;; The two namespaces never cross, even when a program reuses a name.
  (check-equal?
   (term (rename-ordinary (let (bind () (a)) (write-int a 1) (finish a)) a z))
   (term (let (bind () (a)) (write-int a 1) (finish a))))
  (check-equal?
   (term (rename-resource (let (bind () (b)) (write-int a 1) (finish b)) a z))
   (term (let (bind () (b)) (write-int z 1) (finish b))))

  ;; The successor may reuse the source's name; the occurrence in the body
  ;; then belongs to the successor.
  (check-equal?
   (term (rename-resource (let (bind () (w)) (write-int w 1) (finish w)) w q))
   (term (let (bind () (w)) (write-int q 1) (finish w))))

  ;; Each switch branch stops at its own binder.
  (check-equal?
   (term (rename-resource
          (switch c (left c (finish c)) (right d (finish c))) c q))
   (term (switch q (left c (finish c)) (right d (finish q)))))

  (check-equal? (term (resource-mode (Read (row () closed)))) (term affine))
  (check-equal? (term (resource-mode (Write (row () closed) Int))) (term linear))
  (check-equal?
   (term (lookup-signature g ((f (def (sig () () () ()) (bind () ()) (return (1) ()))))))
   #f))
