#lang racket

;; The span candidate: the design the selected core is being compared against.
;;
;; Here a serialized value is a typed span `[start, end)` into an immutable
;; store.  Observing a span yields sub-spans rather than advancing a cursor, so
;; spans are unrestricted -- they can be duplicated and dropped freely, with no
;; affine or linear discipline anywhere.
;;
;; What that costs shows up in `field-spans` below.  With no cursor to have
;; already walked one field, finding where the next field begins means
;; scanning it.  The cursor design pays nothing there, because the
;; cursor that finished one field *is* the position of the next;
;; the price it pays instead is that cursors are substructural.
;;
;; This model shares the shape grammar and the encoding relation with the
;; selected core, so the comparison is between the access disciplines and
;; nothing else.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "layout.rkt")

(provide (all-defined-out))

(define-extended-language Span Shape
  (i ::= natural)
  ;; a typed span into the store
  (sp ::= (span A i i))
  ;; what observing a span reveals
  ;; `integer` is a Redex built-in pattern, so the observation constructors
  ;; are prefixed.
  (obs ::= (obs-int n) (obs-left (sp ...)) (obs-right (sp ...)))
  (se ::= sp obs (pack A v) (view sp) (copy sp))
  ;; store paired with the expression being reduced
  (C ::= (S se))
  (i? ::= i #f)
  (sps? ::= (sp ...) #f))

(define-metafunction Span
  store-slice : S i i -> S
  [(store-slice (cell ...) i_start i_end)
   ,(take (drop (term (cell ...)) (term i_start))
          (max 0 (- (term i_end) (term i_start))))])

(define-metafunction Span
  span-cell-at : S i -> cell or #f
  [(span-cell-at (cell ...) i)
   ,(if (< (term i) (length (term (cell ...))))
        (list-ref (term (cell ...)) (term i))
        #f)])

;; Where the encoding of `A` starting at `i` ends.  Defined through the
;; encoding relation rather than a separate walk, so the two candidate models
;; cannot disagree about layout.
(define-metafunction Span
  scan-end : S A i -> i?
  [(scan-end (cell ...) A i)
   ,(let* ([store (term (cell ...))]
           [suffix (drop store (min (term i) (length store)))]
           [results (judgment-holds (consumes A ,suffix v S_rest) S_rest)])
      (if (= (length results) 1)
          (- (length store) (length (car results)))
          #f))])

;; A span is valid when its shape decodes exactly the cells it delimits.
(define-judgment-form Span
  #:mode (span-valid I I)
  #:contract (span-valid S sp)
  [(consumes A (store-slice S i_start i_end) v ())
   ------------------------------ "valid"
   (span-valid S (span A i_start i_end))])

;; Observing a span.  Every case hands back sub-spans of the same store; no
;; capability is consumed, which is exactly the difference from the protocol
;; core's readers.
;; Named `span-view` rather than `view` because the term constructor
;; `(view sp)` and a judgment form of the same name would collide.
(define-judgment-form Span
  #:mode (span-view I I O)
  #:contract (span-view S sp obs)

  [(where (I n) (span-cell-at S i_start))
   ------------------------------ "integer"
   (span-view S (span Int i_start i_end) (obs-int n))]

  [(where L (span-cell-at S i_start))
   (where i_payload ,(add1 (term i_start)))
   (where (sp ...) (field-spans S (data-fields A left) i_payload))
   ------------------------------ "left"
   (span-view S (span (name A (Data X P_left P_right)) i_start i_end)
              (obs-left (sp ...)))]

  [(where R (span-cell-at S i_start))
   (where i_payload ,(add1 (term i_start)))
   (where (sp ...) (field-spans S (data-fields A right) i_payload))
   ------------------------------ "right"
   (span-view S (span (name A (Data X P_left P_right)) i_start i_end)
              (obs-right (sp ...)))])

;; One span per field.  The scan is the cost of the span representation:
;; finding where a field starts means walking every field before it.
(define-metafunction Span
  field-spans : S P i -> sps?
  [(field-spans S () i) ()]
  [(field-spans S (A A_rest ...) i)
   ((span A i i_next) sp_rest ...)
   (where i_next (scan-end S A i))
   (where (sp_rest ...) (field-spans S (A_rest ...) i_next))]
  [(field-spans S P i) #f])

(define span-reduction
  (reduction-relation
   Span
   #:domain C
   (--> ((cell ...) (pack A v))
        ((cell ... cell_new ...) (span A i_start i_end))
        (judgment-holds (serializes A v (cell_new ...)))
        (where i_start ,(length (term (cell ...))))
        (where i_end ,(+ (length (term (cell ...))) (length (term (cell_new ...)))))
        "pack")

   (--> (S (view sp))
        (S obs)
        (judgment-holds (span-valid S sp))
        (judgment-holds (span-view S sp obs))
        "view")

   (--> ((cell ...) (copy (span A i_start i_end)))
        ((cell ... cell_copy ...) (span A i_new_start i_new_end))
        (judgment-holds (span-valid (cell ...) (span A i_start i_end)))
        (where (cell_copy ...) (store-slice (cell ...) i_start i_end))
        (where i_new_start ,(length (term (cell ...))))
        (where i_new_end ,(+ (length (term (cell ...)))
                             (- (term i_end) (term i_start))))
        "copy")))

(module+ test
  (define sample-tree
    (term (inr ((inl (1)) (inl (2))))))
  (define sample-store (serialize tree-shape sample-tree))

  ;; Packing puts the serialization at the end of the store and returns the
  ;; span that delimits it.
  (check-equal?
   (apply-reduction-relation span-reduction (term (() (pack Int 7))))
   (list (term (((I 7)) (span Int 0 1)))))
  (check-equal?
   (apply-reduction-relation span-reduction
                             (term (,sample-store (pack Int 7))))
   (list (term ((R L (I 1) L (I 2) (I 7)) (span Int 5 6)))))

  (define root (term (span ,tree-shape 0 ,(length sample-store))))
  (check-true (judgment-holds (span-valid ,sample-store ,root)))
  ;; A span whose endpoint does not line up is not valid.
  (check-false (judgment-holds (span-valid ,sample-store (span ,tree-shape 0 3))))

  ;; Viewing the root reveals the node tag and the two sub-spans.  Note the
  ;; scan hidden in the view: the right sub-span starts at 3, which only the
  ;; walk over the left subtree could have found.
  (check-equal?
   (apply-reduction-relation span-reduction (term (,sample-store (view ,root))))
   (list (term (,sample-store (obs-right ((span ,tree-shape 1 3)
                                          (span ,tree-shape 3 5)))))))

  ;; Spans are unrestricted: the same span can be viewed twice, and copying
  ;; one leaves the original intact.
  (check-equal?
   (length (apply-reduction-relation span-reduction (term (,sample-store (view ,root)))))
   1)
  (define copied
    (car (apply-reduction-relation span-reduction (term (,sample-store (copy ,root))))))
  (check-equal? copied
                (term ((R L (I 1) L (I 2) R L (I 1) L (I 2))
                       (span ,tree-shape 5 10))))
  (check-true (judgment-holds (span-valid ,(first copied) ,(second copied))))
  (check-true (judgment-holds (span-valid ,(first copied) ,root))))
