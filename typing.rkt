#lang racket

;; The type system.
;;
;; Typing a term takes an incoming resource context and produces both a result
;; and a *residual* context: what capabilities are still live afterwards.  That
;; second output is where the substructural discipline lives.  Every construct
;; that touches a cursor removes the name it consumed and produces a
;; successor, so a cursor that has been advanced is simply gone from the
;; context and cannot be used again.
;;
;; The two modes differ in how a scope closes.  A `let` checks it once for
;; every resource it bound (`affine-at`): a reader still bound when the body
;; finishes is dropped, but a writer may not be.  That one premise is
;; linearity: a half-built value must not be abandoned.
;;
;; Branching constructs require both branches to agree on the residual as well
;; as on the result, so a program cannot consume a writer down one path and
;; leave it live down the other.
;;
;; Binders are named, and a rule opens a scope by renaming the binder to a
;; name fresh for the context before checking under it.  The residual it
;; produces therefore mentions the fresh name, which is what the rule removes.
;;
;; The judgment is algorithmic: with the signatures, contexts, and term as
;; inputs, the result and residual are determined.  `build-derivations` on it
;; gives a full typing derivation.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "layout.rkt"
         "protocol.rkt"
         "capability.rkt"
         "syntax.rkt"
         "match.rkt")

(provide (all-defined-out))

(define-extended-language Typing Match
  (Gamma ::= ((x T) ...))
  (Delta ::= ((r R) ...))
  (T? ::= T #f)
  (R? ::= R #f)
  (Rs? ::= (R ...) #f))

;; ---------------------------------------------------------------------------
;; Contexts
;; ---------------------------------------------------------------------------

(define-metafunction Typing
  lookup-ordinary : Gamma x -> T?
  [(lookup-ordinary () x) #f]
  [(lookup-ordinary ((x T) (x_rest T_rest) ...) x) T]
  [(lookup-ordinary ((x_1 T_1) (x_rest T_rest) ...) x)
   (lookup-ordinary ((x_rest T_rest) ...) x)])

(define-metafunction Typing
  lookup-resource : Delta r -> R?
  [(lookup-resource () r) #f]
  [(lookup-resource ((r R) (r_rest R_rest) ...) r) R]
  [(lookup-resource ((r_1 R_1) (r_rest R_rest) ...) r)
   (lookup-resource ((r_rest R_rest) ...) r)])

(define-metafunction Typing
  remove-resource : Delta r -> Delta
  [(remove-resource () r) ()]
  [(remove-resource ((r R) (r_rest R_rest) ...) r) ((r_rest R_rest) ...)]
  [(remove-resource ((r_1 R_1) (r_rest R_rest) ...) r)
   ((r_1 R_1) (r_2 R_2) ...)
   (where ((r_2 R_2) ...) (remove-resource ((r_rest R_rest) ...) r))])

(define-metafunction Typing
  lookup-resources : Delta (r ...) -> Rs?
  [(lookup-resources Delta ()) ()]
  [(lookup-resources Delta (r r_rest ...))
   (R R_rest ...)
   (where R (lookup-resource Delta r))
   (where (R_rest ...) (lookup-resources Delta (r_rest ...)))]
  [(lookup-resources Delta (r ...)) #f])

(define-metafunction Typing
  remove-resources : Delta (r ...) -> Delta
  [(remove-resources Delta ()) Delta]
  [(remove-resources Delta (r r_rest ...))
   (remove-resources (remove-resource Delta r) (r_rest ...))])

(define-metafunction Typing
  extend-ordinary : Gamma x T -> Gamma
  [(extend-ordinary ((x_g T_g) ...) x T) ((x T) (x_g T_g) ...)])

(define-metafunction Typing
  extend-resource : Delta r R -> Delta
  [(extend-resource ((r_d R_d) ...) r R) ((r R) (r_d R_d) ...)])

(define-metafunction Typing
  extend-ordinary-many : Gamma (x ...) (T ...) -> Gamma
  [(extend-ordinary-many ((x_g T_g) ...) (x ...) (T ...))
   ((x T) ... (x_g T_g) ...)])

(define-metafunction Typing
  extend-resource-many : Delta (r ...) (R ...) -> Delta
  [(extend-resource-many ((r_d R_d) ...) (r ...) (R ...))
   ((r R) ... (r_d R_d) ...)])

;; No writer is left dangling.  Required wherever control leaves for good.
(define-judgment-form Typing
  #:mode (context-all-affine I)
  #:contract (context-all-affine Delta)
  [------------------------------ "nil"
   (context-all-affine ())]
  [(where affine (resource-mode R))
   (context-all-affine ((r_rest R_rest) ...))
   ------------------------------ "cons"
   (context-all-affine ((r R) (r_rest R_rest) ...))])

;; Each of these names, if still bound, is affine.  Used to close the scope of
;; the resources a call handed back.
(define-judgment-form Typing
  #:mode (affine-at I I)
  #:contract (affine-at Delta (r ...))
  [------------------------------ "nil"
   (affine-at Delta ())]
  [(where #f (lookup-resource Delta r))
   (affine-at Delta (r_rest ...))
   ------------------------------ "absent"
   (affine-at Delta (r r_rest ...))]
  [(where R (lookup-resource Delta r))
   (where affine (resource-mode R))
   (affine-at Delta (r_rest ...))
   ------------------------------ "affine"
   (affine-at Delta (r r_rest ...))])

;; ---------------------------------------------------------------------------
;; Freshness
;;
;; A binder keeps its own name when that name is not bound in the context, and
;; is renamed apart when it is.  A new name must avoid the context, every name
;; in the term it opens (so it cannot capture a free occurrence, or collide
;; with a binder inside, which `rename-ordinary` does not rename around), and
;; the other binders of the same vector (which `rename-ordinary-many` renames
;; one after another).  This is Rocq's side condition on a binding rule:
;; fresh for the context and not free in the scoped term.
;; ---------------------------------------------------------------------------

(define (choose-binders domain scoped names)
  (let loop ([names names] [taken '()])
    (match names
      ['() (reverse taken)]
      [(cons name rest)
       (define chosen
         (if (or (memq name domain) (memq name taken))
             (variable-not-in (list domain scoped names taken) name)
             name))
       (loop rest (cons chosen taken))])))

(define-metafunction Typing
  fresh-ordinary-name : Gamma e x -> x
  [(fresh-ordinary-name ((x_g T_g) ...) e x)
   ,(car (choose-binders (term (x_g ...)) (term e) (list (term x))))])

(define-metafunction Typing
  fresh-resource-name : Delta e r -> r
  [(fresh-resource-name ((r_d R_d) ...) e r)
   ,(car (choose-binders (term (r_d ...)) (term e) (list (term r))))])

(define-metafunction Typing
  fresh-ordinary-names : Gamma e (x ...) -> (x ...)
  [(fresh-ordinary-names ((x_g T_g) ...) e (x ...))
   ,(choose-binders (term (x_g ...)) (term e) (term (x ...)))])

(define-metafunction Typing
  fresh-resource-names : Delta e (r ...) -> (r ...)
  [(fresh-resource-names ((r_d R_d) ...) e (r ...))
   ,(choose-binders (term (r_d ...)) (term e) (term (r ...)))])

(define-judgment-form Typing
  #:mode (distinct I)
  #:contract (distinct (any ...))
  [(side-condition ,(let ([names (term (any ...))])
                      (= (length names) (length (remove-duplicates names)))))
   ------------------------------ "distinct"
   (distinct (any ...))])

;; ---------------------------------------------------------------------------
;; Atoms
;; ---------------------------------------------------------------------------

(define-judgment-form Typing
  #:mode (atom-typing I I O)
  #:contract (atom-typing Gamma atom T)
  [------------------------------ "integer"
   (atom-typing Gamma n Int)]
  [(where T (lookup-ordinary Gamma x))
   ------------------------------ "variable"
   (atom-typing Gamma x T)])

(define-judgment-form Typing
  #:mode (atoms-typing I I O)
  #:contract (atoms-typing Gamma (atom ...) (T ...))
  [------------------------------ "nil"
   (atoms-typing Gamma () ())]
  [(atom-typing Gamma atom T)
   (atoms-typing Gamma (atom_rest ...) (T_rest ...))
   ------------------------------ "cons"
   (atoms-typing Gamma (atom atom_rest ...) (T T_rest ...))])

;; ---------------------------------------------------------------------------
;; Terms
;; ---------------------------------------------------------------------------

(define-judgment-form Typing
  #:mode (term-typing I I I I O O)
  #:contract (term-typing Sigma Gamma Delta e res Delta)

  ;; Hand back values and an ordered list of capabilities.  Any other
  ;; resource passes through in the residual.
  [(atoms-typing Gamma (atom ...) (T ...))
   (distinct (r ...))
   (where (R ...) (lookup-resources Delta (r ...)))
   (where Delta_out (remove-resources Delta (r ...)))
   ------------------------------ "return"
   (term-typing Sigma Gamma Delta (return (atom ...) (r ...))
                (bundle (T ...) (R ...)) Delta_out)]

  ;; The right-hand side's residual is what the body starts from, together
  ;; with the resources it produced under their new names.  Every one of those
  ;; that is still bound when the body finishes must be a reader: a writer has
  ;; to be consumed.
  [(term-typing Sigma Gamma Delta e_rhs (bundle (T ...) (R ...)) Delta_middle)
   (side-condition ,(= (length (term (x_bind ...))) (length (term (T ...)))))
   (side-condition ,(= (length (term (r_bind ...))) (length (term (R ...)))))
   (distinct (x_bind ...))
   (distinct (r_bind ...))
   (where (x_fresh ...) (fresh-ordinary-names Gamma e_body (x_bind ...)))
   (where (r_fresh ...) (fresh-resource-names Delta_middle e_body (r_bind ...)))
   (where e_scoped (open-let-body e_body (x_bind ...) (x_fresh ...)
                                  (r_bind ...) (r_fresh ...)))
   (term-typing Sigma
                (extend-ordinary-many Gamma (x_fresh ...) (T ...))
                (extend-resource-many Delta_middle (r_fresh ...) (R ...))
                e_scoped res Delta_scoped)
   (affine-at Delta_scoped (r_fresh ...))
   (where Delta_out (remove-resources Delta_scoped (r_fresh ...)))
   ------------------------------ "let"
   (term-typing Sigma Gamma Delta
                (let (bind (x_bind ...) (r_bind ...)) e_rhs e_body)
                res Delta_out)]

  ;; Both branches start from the same capabilities and must agree on the
  ;; result and on what they leave behind.
  [(atom-typing Gamma atom_lhs Int)
   (atom-typing Gamma atom_rhs Int)
   (term-typing Sigma Gamma Delta e_true res Delta_out)
   (term-typing Sigma Gamma Delta e_false res Delta_out)
   ------------------------------ "if"
   (term-typing Sigma Gamma Delta (if cmp atom_lhs atom_rhs e_true e_false)
                res Delta_out)]

  ;; The reader is consumed, and each branch binds a successor at the fields
  ;; of its constructor, in front of whatever followed the datatype.  The
  ;; successor is affine, so closing its scope just drops it.  The repeated
  ;; `res` and `Delta_out` make the branches agree.
  [(where (Read (row ((name A_data (Data X P_left P_right)) A_tail ...) tl))
          (lookup-resource Delta r_src))
   (where Delta_rest (remove-resource Delta r_src))
   (where (A_lhs ...) (data-fields A_data left))
   (where (A_rhs ...) (data-fields A_data right))
   (where r_lfresh (fresh-resource-name Delta_rest e_lhs r_lhs))
   (where e_lscoped (rename-resource e_lhs r_lhs r_lfresh))
   (term-typing
    Sigma Gamma
    (extend-resource Delta_rest r_lfresh (Read (row (A_lhs ... A_tail ...) tl)))
    e_lscoped res Delta_lscoped)
   (where Delta_out (remove-resource Delta_lscoped r_lfresh))
   (where r_rfresh (fresh-resource-name Delta_rest e_rhs r_rhs))
   (where e_rscoped (rename-resource e_rhs r_rhs r_rfresh))
   (term-typing
    Sigma Gamma
    (extend-resource Delta_rest r_rfresh (Read (row (A_rhs ... A_tail ...) tl)))
    e_rscoped res Delta_rscoped)
   (where Delta_out (remove-resource Delta_rscoped r_rfresh))
   ------------------------------ "switch"
   (term-typing Sigma Gamma Delta
                (switch r_src (left r_lhs e_lhs) (right r_rhs e_rhs))
                res Delta_out)]

  [(atom-typing Gamma atom_lhs Int)
   (atom-typing Gamma atom_rhs Int)
   ------------------------------ "arith"
   (term-typing Sigma Gamma Delta (arith aop atom_lhs atom_rhs)
                (bundle (Int) ()) Delta)]

  ;; Each cursor step reads its action off the head of the row's prefix,
  ;; consumes the cursor, and produces its successor.  An empty prefix has no
  ;; head, so a cursor whose prefix is used up and whose tail is abstract can
  ;; do nothing: what follows is not yet known.
  [(where (Read (row (Int A_tail ...) tl)) (lookup-resource Delta r))
   ------------------------------ "read-int"
   (term-typing Sigma Gamma Delta (read-int r)
                (bundle (Int) ((Read (row (A_tail ...) tl))))
                (remove-resource Delta r))]

  [(atom-typing Gamma atom Int)
   (where (Write (row (Int A_tail ...) tl) A_result) (lookup-resource Delta r))
   ------------------------------ "write-int"
   (term-typing Sigma Gamma Delta (write-int r atom)
                (bundle () ((Write (row (A_tail ...) tl) A_result)))
                (remove-resource Delta r))]

  [(where (Write (row ((name A_data (Data X P_left P_right)) A_tail ...) tl) A_result)
          (lookup-resource Delta r))
   (where (A_field ...) (data-fields A_data left))
   ------------------------------ "write-left"
   (term-typing Sigma Gamma Delta (write-left r)
                (bundle () ((Write (row (A_field ... A_tail ...) tl) A_result)))
                (remove-resource Delta r))]

  [(where (Write (row ((name A_data (Data X P_left P_right)) A_tail ...) tl) A_result)
          (lookup-resource Delta r))
   (where (A_field ...) (data-fields A_data right))
   ------------------------------ "write-right"
   (term-typing Sigma Gamma Delta (write-right r)
                (bundle () ((Write (row (A_field ... A_tail ...) tl) A_result)))
                (remove-resource Delta r))]

  ;; Opening a finished value gives a reader owing exactly that shape, on a
  ;; closed row: nothing follows it.
  [(atom-typing Gamma atom (Ser A))
   (closed-shape-wf A)
   ------------------------------ "open"
   (term-typing Sigma Gamma Delta (open atom)
                (bundle () ((Read (closed-row (A))))) Delta)]

  [(closed-shape-wf A)
   ------------------------------ "new"
   (term-typing Sigma Gamma Delta (new A)
                (bundle () ((Write (closed-row (A)) A))) Delta)]

  ;; Only an empty prefix on a closed row is finished.  An abstract tail could
  ;; still be instantiated with more to write.
  [(where (Write (row () closed) A) (lookup-resource Delta r))
   ------------------------------ "finish"
   (term-typing Sigma Gamma Delta (finish r)
                (bundle ((Ser A)) ()) (remove-resource Delta r))]

  ;; A call hands the named capabilities over, binds the callee's frames
  ;; against their actual rows, and produces the declared outputs
  ;; instantiated at that binding.
  [(where df (lookup-signature f Sigma))
   (where (sig (T_in ...) (R_in ...) (T_out ...) (R_out ...))
          (signature-of df))
   (atoms-typing Gamma (atom ...) (T_in ...))
   (distinct (r_arg ...))
   (where (R_actual ...) (lookup-resources Delta (r_arg ...)))
   (where theta (match-resource-types (R_in ...) (R_actual ...)))
   ------------------------------ "call"
   (term-typing Sigma Gamma Delta (call f (atom ...) (r_arg ...))
                (bundle (T_out ...) (instantiate-resource-types theta (R_out ...)))
                (remove-resources Delta (r_arg ...)))])

(define-judgment-form Typing
  #:mode (closed-term-typing I I O)
  #:contract (closed-term-typing Sigma e res)
  [(term-typing Sigma () () e res Delta_out)
   (context-all-affine Delta_out)
   ------------------------------ "closed"
   (closed-term-typing Sigma e res)])

;; ---------------------------------------------------------------------------
;; Signatures
;;
;; A signature's declared rows have to be usable.  Every prefix must be closed,
;; every input row must be closed or end in its own frame, and every output row
;; must be closed or end in the frame of some input -- so every frame an output
;; mentions is bound at every call site.
;; ---------------------------------------------------------------------------

;; The input at position `natural` is closed or ends in its own frame.
(define-judgment-form Typing
  #:mode (inputs-framed-from I I)
  #:contract (inputs-framed-from natural (R ...))
  [------------------------------ "nil"
   (inputs-framed-from natural ())]
  [(row-wf (resource-type-row R))
   (where (row P tl) (resource-type-row R))
   (side-condition ,(member (term tl) (list 'closed (list 'tvar (term natural)))))
   (inputs-framed-from ,(add1 (term natural)) (R_rest ...))
   ------------------------------ "cons"
   (inputs-framed-from natural (R R_rest ...))])

(define-judgment-form Typing
  #:mode (tail-in-scope I I)
  #:contract (tail-in-scope natural tl)
  [------------------------------ "closed"
   (tail-in-scope natural closed)]
  [(side-condition ,(< (term natural_index) (term natural_count)))
   ------------------------------ "var"
   (tail-in-scope natural_count (tvar natural_index))])

(define-judgment-form Typing
  #:mode (outputs-in-scope I I)
  #:contract (outputs-in-scope natural (R ...))
  [------------------------------ "nil"
   (outputs-in-scope natural ())]
  [(row-wf (resource-type-row R))
   (tail-in-scope natural (row-tail (resource-type-row R)))
   (outputs-in-scope natural (R_rest ...))
   ------------------------------ "cons"
   (outputs-in-scope natural (R R_rest ...))])

;; A definition checks when its body, given the declared inputs, yields
;; exactly the declared outputs with nothing linear left over.  The inputs'
;; frames stay abstract throughout: checking against an abstract frame is what
;; makes one derivation serve every call site.  The environment is checked
;; against itself, which is what admits recursion -- and is why type safety
;; here says nothing about termination.
;;
;; That one derivation really does serve every call site: Rocq's
;; `definition_entry_wf_from_abstract_check` derives the semantic condition
;; preservation consumes -- a derivation at every tail instantiation and every
;; choice of parameter names -- from exactly this check, using
;; `term_typing_instantiate` for the rows and `body_scope_typing_rename` for
;; the names.  It also asks that the body be a closed term.  Here that is free:
;; binders are named, so an open body simply fails to type.  With locally
;; nameless binders it is not, because the machine picks a callee's parameter
;; names without looking at its body, and a body with a free name of its own
;; could have it captured.
(define-judgment-form Typing
  #:mode (definition-wf I I)
  #:contract (definition-wf Sigma df)
  [(where (sig (T_in ...) (R_in ...) (T_out ...) (R_out ...)) sg)
   (inputs-framed-from 0 (R_in ...))
   (outputs-in-scope ,(length (term (R_in ...))) (R_out ...))
   (side-condition ,(= (length (term (x_param ...))) (length (term (T_in ...)))))
   (side-condition ,(= (length (term (r_param ...))) (length (term (R_in ...)))))
   (distinct (x_param ...))
   (distinct (r_param ...))
   (term-typing Sigma
                ((x_param T_in) ...)
                ((r_param R_in) ...)
                e (bundle (T_out ...) (R_out ...)) Delta_out)
   (context-all-affine Delta_out)
   ------------------------------ "definition"
   (definition-wf Sigma (def sg (bind (x_param ...) (r_param ...)) e))])

(define-judgment-form Typing
  #:mode (signature-env-wf I I)
  #:contract (signature-env-wf Sigma Sigma)
  [------------------------------ "nil"
   (signature-env-wf Sigma ())]
  [(definition-wf Sigma df)
   (signature-env-wf Sigma ((f_rest df_rest) ...))
   ------------------------------ "cons"
   (signature-env-wf Sigma ((f df) (f_rest df_rest) ...))])

;; ---------------------------------------------------------------------------
;; Entry points
;; ---------------------------------------------------------------------------

;; Whether every definition in an environment checks against that environment.
(define (signature-env-ok? sigma)
  (judgment-holds (signature-env-wf ,sigma ,sigma)))

;; The result types a closed term can have: a one-element list when it checks,
;; empty when it does not.
(define (type-of sigma expression)
  (judgment-holds (closed-term-typing ,sigma ,expression res) res))

;; The typing derivations of a closed term, as `derivation` structures.  Pass
;; one to `show-derivations` from `redex/gui` to see it drawn.
(define (typing-derivations sigma expression)
  (build-derivations (closed-term-typing ,sigma ,expression res)))

(module+ test
  (define build-seven
    (term (let (bind () (w)) (new Int)
            (let (bind () (w2)) (write-int w 7)
              (finish w2)))))
  (check-equal? (type-of (term ()) build-seven)
                (list (term (bundle ((Ser Int)) ()))))

  ;; A writer left unfinished cannot leave its scope.
  (check-equal?
   (type-of (term ()) (term (let (bind () (w)) (new Int) (return (1) ()))))
   '())
  ;; Nor can one be finished before its protocol is exhausted.
  (check-equal?
   (type-of (term ())
            (term (let (bind () (w)) (new (Data X (Int) (Int))) (finish w))))
   '())
  ;; Nor used twice: `w` is gone once `w2` is bound.
  (check-equal?
   (type-of (term ())
            (term (let (bind () (w)) (new Int)
                    (let (bind () (w2)) (write-int w 7)
                      (let (bind () (w3)) (write-int w 8)
                        (finish w3))))))
   '())

  ;; Readers are affine, so opening one and ignoring it is fine.
  (define (after-seven body)
    (term (let (bind (s) ()) ,build-seven
            (let (bind () (rd)) (open s) ,body))))
  (check-equal? (type-of (term ()) (after-seven (term (return (1) ()))))
                (list (term (bundle (Int) ()))))
  (check-equal? (type-of (term ()) (after-seven (term (read-int rd))))
                (list (term (bundle (Int) ((Read (row () closed)))))))
  (check-equal?
   (type-of (term ())
            (after-seven (term (let (bind (v) (rd2)) (read-int rd)
                                 (return (v) ())))))
   (list (term (bundle (Int) ()))))

  ;; Both branches of a switch agree on the result.
  (check-equal?
   (type-of (term ())
            (term (let (bind (s) ())
                       (let (bind () (w)) (new (Data X (Int) (Int)))
                         (let (bind () (w2)) (write-left w)
                           (let (bind () (w3)) (write-int w2 1)
                             (finish w3))))
                    (let (bind () (rd)) (open s)
                      (switch rd
                        (left rd1 (let (bind (v) (rd2)) (read-int rd1)
                                    (return (v) ())))
                        (right rd1 (let (bind (v) (rd2)) (read-int rd1)
                                     (return (v) ()))))))))
   (list (term (bundle (Int) ()))))

  ;; A writer whose remaining row ends in an abstract tail cannot be
  ;; finished: instantiating that tail could still call for more to write.
  (check-false
   (judgment-holds
    (term-typing () () ((wt (Write (row () (tvar 0)) Int))) (finish wt)
                 res Delta_out)))
  (check-true
   (judgment-holds
    (term-typing () () ((wt (Write (row () closed) Int))) (finish wt)
                 res Delta_out)))

  ;; Shape well-formedness is enforced where a writer is created.
  (check-equal?
   (type-of (term ()) (term (let (bind () (w)) (new X) (finish w))))
   '())

  (check-equal?
   (type-of (term ()) (term (arith add 1 2)))
   (list (term (bundle (Int) ()))))
  (check-equal? (type-of (term ()) (term (return (v) ()))) '())

  ;; A derivation is available, with the rule names on it.
  (define derivations (typing-derivations (term ()) build-seven))
  (check-equal? (length derivations) 1)
  (check-equal? (derivation-name (car derivations)) "closed")
  (check-equal? (derivation-name (car (derivation-subs (car derivations))))
                "let")

  ;; Signature well-formedness rejects rows that could never be matched or
  ;; solved.  Each of these is the identity traversal -- hand the reader
  ;; straight back -- so only the declared rows are under test.
  (define (identity-env R)
    (term ((g (def (sig () (,R) () (,R)) (bind () (rd))
                (return () (rd)))))))
  (check-true
   (signature-env-ok? (identity-env (term (Read (row (Int Int) (tvar 0)))))))
  (check-true
   (signature-env-ok? (identity-env (term (Read (row (Int Int) closed))))))
  ;; An input's row ends in its own frame, not another input's.
  (check-false
   (signature-env-ok? (identity-env (term (Read (row (Int) (tvar 1)))))))
  ;; An output may only end in the frame of an input that exists.
  (check-false
   (signature-env-ok?
    (term ((g (def (sig () () () ((Read (row () (tvar 0)))))
                (bind () ()) (return () ())))))))
  ;; An open shape in a declared row is not well formed.
  (check-false
   (signature-env-ok? (identity-env (term (Read (row (X) (tvar 0)))))))

  ;; Renaming a binder apart never captures a free name.  The inner `x`
  ;; shadows the outer one, so it is renamed; the new name must not be the
  ;; `x1` that occurs free, or this unbound `x1` would type.
  (check-equal?
   (type-of (term ())
            (term (let (bind (x) ()) (arith add 1 2)
                    (let (bind (x) ()) (arith add 1 2)
                      (return (x1) ())))))
   '())
  ;; The same for a resource binder.  The outer `w` is a reader, so dropping
  ;; it is fine; the inner `w` shadows it and is renamed, and must not become
  ;; the free `w1`.
  (check-equal?
   (type-of (term ())
            (term (let (bind (s) ()) ,build-seven
                    (let (bind () (w)) (open s)
                      (let (bind () (w)) (new Int)
                        (let (bind () (k)) (write-int w1 7)
                          (finish k)))))))
   '())

  ;; Finishing one writer while another is live is fine: the live one passes
  ;; through in the residual and is consumed later.
  (check-equal?
   (type-of (term ())
            (term (let (bind () (w)) (new Int)
                    (let (bind (s) ()) ,build-seven
                      (let (bind () (rd)) (open s)
                        (let (bind (v) (rd2)) (read-int rd)
                          (let (bind () (w2)) (write-int w v)
                            (finish w2))))))))
   (list (term (bundle ((Ser Int)) ()))))
  ;; But the writer that `finish` leaves live still has to be consumed.
  (check-equal?
   (type-of (term ())
            (term (let (bind () (w)) (new Int) ,build-seven)))
   '())
  ;; A return that leaves a writer behind types, but the writer's scope
  ;; rejects it: here the parameter `wt` is never handed back.
  (check-false
   (signature-env-ok?
    (term ((f (def (sig () ((Write (row (Int) closed) Int)) () ())
                (bind () (wt))
                (return () ())))))))
  (check-equal?
   (type-of (term ()) (term (let (bind () (w)) (new Int) (return () ()))))
   '())
  ;; A let may hand a finished value and a live reader to its body at once.
  (check-equal?
   (type-of (term ())
            (term (let (bind (s) ()) ,build-seven
                    (let (bind () (rd)) (open s)
                      (let (bind (t) (rd2))
                           (let (bind () (b)) (new Int)
                             (let (bind (v) (rd1)) (read-int rd)
                               (let (bind () (b2)) (write-int b v)
                                 (let (bind (t) ()) (finish b2)
                                   (return (t) (rd1))))))
                        (return (t) ()))))))
   (list (term (bundle ((Ser Int)) ())))))
