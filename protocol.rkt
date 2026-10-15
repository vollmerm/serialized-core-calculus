#lang racket

;; Protocols and rows: what a cursor still owes.
;;
;; A protocol is a list of shapes still to be traversed, left to right.  Its
;; head *is* the next action: an integer cell, or the tag of a datatype.  No
;; shape former takes zero cells or hides another in front of it, so there is
;; nothing to normalize, and a step on a cursor only ever looks at the first
;; element.  Taking a tag replaces the datatype at the head by the fields of
;; the chosen constructor, which keeps the protocol flat.
;;
;; A *row* is a protocol prefix followed by an optional tail variable.  Rows
;; are what recursive function signatures quantify over: "this cursor is
;; positioned at a tree, followed by whatever else the caller had lined up".
;; A concrete cursor always carries a closed row.
;;
;; The typing rules look at the prefix only.  When the prefix is empty, the
;; next action would have to come from the tail, and an abstract tail cannot
;; say what it is -- so no rule applies.  That is what makes a function
;; typechecked once at an abstract tail valid at every tail it is called with:
;; appending to a row never changes a head the prefix already had.

(require redex/reduction-semantics
         rackunit
         "shape.rkt")

(provide (all-defined-out))

(define-extended-language Protocol Shape
  (tl ::= closed (tvar natural))
  ;; A row.  The nonterminal is `rho` because Redex reads a leading `row`
  ;; inside a production as a reference to the nonterminal of that name.
  (rho ::= (row P tl))
  (P? ::= P #f))

(define-metafunction Protocol
  closed-row : P -> rho
  [(closed-row P) (row P closed)])

(define-metafunction Protocol
  row-prefix : rho -> P
  [(row-prefix (row P tl)) P])

(define-metafunction Protocol
  row-tail : rho -> tl
  [(row-tail (row P tl)) tl])

;; Advance a row: new prefix, same tail.
(define-metafunction Protocol
  row-with-prefix : rho P -> rho
  [(row-with-prefix (row P_old tl) P_new) (row P_new tl)])

(define-judgment-form Protocol
  #:mode (row-wf I)
  #:contract (row-wf rho)
  [(protocol-wf P)
   ------------------------------ "row"
   (row-wf (row P tl))])

(module+ test
  (check-equal? (term (closed-row (Int))) (term (row (Int) closed)))
  (check-equal? (term (row-with-prefix (row (Int) (tvar 0)) ()))
                (term (row () (tvar 0))))
  (check-true (judgment-holds (row-wf (row (,tree-shape) (tvar 0)))))
  (check-false (judgment-holds (row-wf (row (X) closed)))))
