#lang racket

;; Matching a call site against a function signature.
;;
;; A recursive function is declared over rows that end in *frames*: "give me
;; a reader positioned at a tree followed by whatever you had after it, and I
;; will give you back a reader positioned at that".  Each input resource has
;; its own frame, `(tvar j)` for the input at position j; an input row is
;; either closed or ends in its own frame, and an output row may end in the
;; frame of any input.  At a call site each formal input is matched against
;; the actual resource passed for it, and its frame is bound to what is left.
;;
;; That solution is what makes a self-recursive traversal work.  Descending
;; into the left subtree of a node, the reader is positioned at `(Tree Tree)`.
;; Matching the formal prefix `(Tree)` against it consumes one `Tree` and binds
;; frame 0 to the leftover `(Tree)` -- so the reader handed back is positioned
;; exactly at the sibling, with no offset stored anywhere.
;;
;; Protocols are flat lists, so matching a prefix is literally that: the formal
;; prefix has to be the first elements of the actual one, compared shape by
;; shape.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "protocol.rkt"
         "capability.rkt"
         "syntax.rkt")

(provide (all-defined-out))

(define-extended-language Match Syntax
  ;; What each input's frame was bound to, by position.
  (theta ::= (rho ...))
  (theta? ::= theta #f)
  (rho? ::= rho #f))

;; The unmatched actual suffix, if the formal prefix is a prefix of it.
(define-metafunction Match
  match-prefix : P P -> P?
  [(match-prefix () P) P]
  ;; The repeated `A` is the comparison.
  [(match-prefix (A A_formal ...) (A A_actual ...))
   (match-prefix (A_formal ...) (A_actual ...))]
  [(match-prefix P_1 P_2) #f])

;; A closed formal demands the actual row be exhausted and closed too.  A
;; framed formal absorbs whatever is left, including the actual row's own tail.
(define-metafunction Match
  match-row : rho rho -> rho?
  [(match-row (row P_formal closed) (row P_actual closed))
   (row () closed)
   (where () (match-prefix P_formal P_actual))]
  [(match-row (row P_formal (tvar natural)) (row P_actual tl))
   (row P_remainder tl)
   (where P_remainder (match-prefix P_formal P_actual))]
  [(match-row rho_1 rho_2) #f])

;; A reader matches a reader and a writer a writer; writers must also agree on
;; the shape being built, since that is what the finished value will be.
(define-metafunction Match
  match-resource-type : R R -> rho?
  [(match-resource-type (Read rho_formal) (Read rho_actual))
   (match-row rho_formal rho_actual)]
  [(match-resource-type (Write rho_formal A) (Write rho_actual A))
   (match-row rho_formal rho_actual)]
  [(match-resource-type R_1 R_2) #f])

;; Each formal against the actual in the same position.
(define-metafunction Match
  match-resource-types : (R ...) (R ...) -> theta?
  [(match-resource-types () ()) ()]
  [(match-resource-types (R_formal R_formals ...) (R_actual R_actuals ...))
   (rho rho_rest ...)
   (where rho (match-resource-type R_formal R_actual))
   (where (rho_rest ...) (match-resource-types (R_formals ...) (R_actuals ...)))]
  [(match-resource-types (R_1 ...) (R_2 ...)) #f])

;; Instantiating a declared output row: the row its frame was bound to is
;; appended, which is how the caller learns where the callee left its cursors.
(define-metafunction Match
  instantiate-row : theta rho -> rho
  [(instantiate-row theta (row P closed)) (row P closed)]
  [(instantiate-row (rho_bound ...) (row (A ...) (tvar natural)))
   (row (A ... A_bound ...) tl_bound)
   (side-condition (< (term natural) (length (term (rho_bound ...)))))
   (where (row (A_bound ...) tl_bound)
          ,(list-ref (term (rho_bound ...)) (term natural)))]
  [(instantiate-row theta rho) rho])

(define-metafunction Match
  instantiate-resource-type : theta R -> R
  [(instantiate-resource-type theta (Read rho))
   (Read (instantiate-row theta rho))]
  [(instantiate-resource-type theta (Write rho A))
   (Write (instantiate-row theta rho) A)])

(define-metafunction Match
  instantiate-resource-types : theta (R ...) -> (R ...)
  [(instantiate-resource-types theta (R ...))
   ((instantiate-resource-type theta R) ...)])

(module+ test
  ;; A closed formal row must consume the whole actual row.
  (check-equal? (term (match-row (row (Int) closed) (row (Int) closed)))
                (term (row () closed)))
  (check-equal? (term (match-row (row (Int) closed) (row (Int Int) closed)))
                (term #f))

  ;; A frame absorbs the remainder along with the actual row's tail.
  (check-equal? (term (match-row (row (Int) (tvar 0)) (row (Int Int) closed)))
                (term (row (Int) closed)))
  (check-equal?
   (term (match-row (row (,tree-shape) (tvar 0)) (row (,tree-shape) (tvar 3))))
   (term (row () (tvar 3))))

  ;; The step a recursive traversal depends on: descending into a node, the
  ;; formal `(Tree)` matches the first of the two subtrees and the sibling is
  ;; what the frame is bound to.
  (check-equal?
   (term (match-row (row (,tree-shape) (tvar 0))
                    (row (,tree-shape ,tree-shape) closed)))
   (term (row (,tree-shape) closed)))
  (check-equal?
   (term (instantiate-row ((row (,tree-shape) closed)) (row () (tvar 0))))
   (term (row (,tree-shape) closed)))

  ;; Each input is matched on its own, and its frame bound by position.
  (check-equal?
   (term (match-resource-types ((Read (row (Int) (tvar 0)))
                                (Read (row (Int) (tvar 1))))
                               ((Read (row (Int Int) closed))
                                (Read (row (Int) closed)))))
   (term ((row (Int) closed) (row () closed))))

  ;; Readers do not match writers, and writers must build the same shape.
  (check-equal?
   (term (match-resource-type (Read (row (Int) closed))
                              (Write (row (Int) closed) Int)))
   (term #f))
  (check-equal?
   (term (match-resource-type (Write (row (Int) closed) Int)
                              (Write (row (Int) closed) (Data X (Int) (Int)))))
   (term #f))

  (check-equal?
   (term (instantiate-resource-types ((row (Int) closed))
                                     ((Write (row () (tvar 0)) Int))))
   (term ((Write (row (Int) closed) Int)))))
