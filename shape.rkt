#lang racket

;; Shapes, values, cells.
;;
;; A *shape* is a structural type with two formers: integers, and a datatype
;; with two constructors, each a list of fields.  A datatype binds a variable
;; its fields may use to recur, so `(Data X (Int) (X X))` is a binary tree
;; with integers at the leaves.  A variable nothing refers to makes a plain
;; sum: `(Data X (Int) ())` is an optional integer.
;;
;; A *value* is an integer or a constructor applied to its fields.  A *cell* is
;; one slot of the flat, contiguous encoding a value occupies in memory: an
;; integer cell, or a tag cell saying which constructor was taken.  The fields
;; follow their tag with nothing between them, so the encoding carries no
;; lengths, offsets, or pointers.
;;
;; Because the only way into a datatype's fields is through its tag, every
;; recursive occurrence is preceded by a cell.  That is what lets a cursor find
;; where a value ends by walking it, and it holds by construction: a shape is
;; well formed exactly when it is closed.
;;
;; A *protocol* is a list of shapes still owed, read left to right.  It is the
;; state a cursor carries as it walks an encoding, and it appears here rather
;; than with the cursors because it is layout, not capability.

(require redex/reduction-semantics
         rackunit)

(provide (all-defined-out))

(define-language Shape
  (X ::= variable-not-otherwise-mentioned)
  (n ::= integer)
  (A ::= Int X (Data X P P))
  (v ::= n (inl (v ...)) (inr (v ...)))
  (cell ::= L R (I n))
  (S ::= (cell ...))
  (P ::= (A ...))
  (side ::= left right))

;; ---------------------------------------------------------------------------
;; Well-formedness
;;
;; Closedness is all there is to check.  The variables in scope are the
;; datatypes enclosing the current position.
;; ---------------------------------------------------------------------------

(define-judgment-form Shape
  #:mode (shape-wf I I)
  #:contract (shape-wf (X ...) A)

  [------------------------------ "int"
   (shape-wf (X ...) Int)]

  [(side-condition ,(and (memq (term X) (term (X_scope ...))) #t))
   ------------------------------ "var"
   (shape-wf (X_scope ...) X)]

  [(fields-wf (X X_scope ...) P_left)
   (fields-wf (X X_scope ...) P_right)
   ------------------------------ "data"
   (shape-wf (X_scope ...) (Data X P_left P_right))])

(define-judgment-form Shape
  #:mode (fields-wf I I)
  #:contract (fields-wf (X ...) P)
  [------------------------------ "nil"
   (fields-wf (X ...) ())]
  [(shape-wf (X ...) A)
   (fields-wf (X ...) (A_rest ...))
   ------------------------------ "cons"
   (fields-wf (X ...) (A A_rest ...))])

(define-judgment-form Shape
  #:mode (closed-shape-wf I)
  #:contract (closed-shape-wf A)
  [(shape-wf () A)
   ------------------------------ "closed"
   (closed-shape-wf A)])

(define-judgment-form Shape
  #:mode (protocol-wf I)
  #:contract (protocol-wf P)
  [(fields-wf () P)
   ------------------------------ "protocol"
   (protocol-wf P)])

;; ---------------------------------------------------------------------------
;; Unfolding
;;
;; Taking a constructor's fields substitutes the datatype for its own
;; variable.  The replacement is always a closed shape, so capture cannot
;; arise; an inner datatype that rebinds the variable shadows it.
;; ---------------------------------------------------------------------------

(define-metafunction Shape
  shape-subst : A X A -> A
  [(shape-subst Int X A_new) Int]
  [(shape-subst X X A_new) A_new]
  [(shape-subst X_1 X A_new) X_1]
  [(shape-subst (Data X P_left P_right) X A_new) (Data X P_left P_right)]
  [(shape-subst (Data X_1 P_left P_right) X A_new)
   (Data X_1 (fields-subst P_left X A_new) (fields-subst P_right X A_new))])

(define-metafunction Shape
  fields-subst : P X A -> P
  [(fields-subst (A ...) X A_new) ((shape-subst A X A_new) ...)])

(define-metafunction Shape
  data-fields : A side -> P
  [(data-fields (Data X P_left P_right) left)
   (fields-subst P_left X (Data X P_left P_right))]
  [(data-fields (Data X P_left P_right) right)
   (fields-subst P_right X (Data X P_left P_right))])

;; ---------------------------------------------------------------------------
;; Shaping
;;
;; Which ordinary values inhabit a shape.  This is the specification the
;; encoding in layout.rkt has to agree with.
;; ---------------------------------------------------------------------------

(define-judgment-form Shape
  #:mode (value-has-shape I I)
  #:contract (value-has-shape A v)

  [------------------------------ "int"
   (value-has-shape Int n)]

  [(values-have-shapes (data-fields (Data X P_left P_right) left) (v ...))
   ------------------------------ "inl"
   (value-has-shape (Data X P_left P_right) (inl (v ...)))]

  [(values-have-shapes (data-fields (Data X P_left P_right) right) (v ...))
   ------------------------------ "inr"
   (value-has-shape (Data X P_left P_right) (inr (v ...)))])

(define-judgment-form Shape
  #:mode (values-have-shapes I I)
  #:contract (values-have-shapes P (v ...))
  [------------------------------ "nil"
   (values-have-shapes () ())]
  [(value-has-shape A v)
   (values-have-shapes (A_rest ...) (v_rest ...))
   ------------------------------ "cons"
   (values-have-shapes (A A_rest ...) (v v_rest ...))])

;; The running example: a binary tree with integers at the leaves.
(define tree-shape (term (Data X (Int) (X X))))

;; A cons-list of integers whose nil is a tag and nothing else.
(define list-shape (term (Data X () (Int X))))

(module+ test
  (check-true (judgment-holds (closed-shape-wf ,tree-shape)))
  (check-true (judgment-holds (closed-shape-wf Int)))
  (check-true (judgment-holds (closed-shape-wf ,list-shape)))
  ;; A stream: well formed, even though it has no finite values.
  (check-true (judgment-holds (closed-shape-wf (Data X (Int X) (Int X)))))
  ;; Datatypes nest, and an inner one may recur through an outer one.
  (check-true
   (judgment-holds (closed-shape-wf (Data X (Int) ((Data Y (X) (Y)))))))
  ;; Open shapes are rejected outright; nothing else can go wrong.
  (check-false (judgment-holds (closed-shape-wf X)))
  (check-false (judgment-holds (closed-shape-wf (Data X (Y) ()))))

  (check-equal? (term (data-fields ,tree-shape right))
                (term (,tree-shape ,tree-shape)))
  (check-equal? (term (data-fields ,list-shape left)) (term ()))

  (check-true
   (judgment-holds (value-has-shape ,tree-shape (inl (1)))))
  (check-true
   (judgment-holds
    (value-has-shape ,tree-shape (inr ((inl (1)) (inl (2)))))))
  (check-false
   (judgment-holds (value-has-shape ,tree-shape (inl ((inl (1)))))))
  (check-false
   (judgment-holds (value-has-shape ,tree-shape (inr ((inl (1))))))))
