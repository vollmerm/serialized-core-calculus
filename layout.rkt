#lang racket

;; The encoding: how a value becomes cells, and how cells become a value
;; again.
;;
;; Both directions are one relation each, so the encoder and the decoder
;; cannot drift apart.  Read with the shape and the value as inputs,
;; `serializes` is the encoder; read with the shape and the cells as inputs,
;; `consumes` is the decoder.
;;
;; `consumes` takes a whole store and hands back what it did not read.  That
;; extra output is the point: a value's encoding is a *prefix* of the cells in
;; front of it, with its siblings following immediately after and no delimiter
;; in between.  Decoding a constructor's fields is decoding the first and
;; handing the leftovers to the next.  This is also why a cursor needs an
;; endpoint to know when it is finished, rather than being able to look for a
;; terminator.

(require redex/reduction-semantics
         rackunit
         "shape.rkt")

(provide (all-defined-out))

(define-judgment-form Shape
  #:mode (serializes I I O)
  #:contract (serializes A v S)

  [------------------------------ "int"
   (serializes Int n ((I n)))]

  ;; The tag, then the fields, with no separator between them.
  [(serializes-fields (data-fields (Data X P_left P_right) left) (v ...) (cell ...))
   ------------------------------ "inl"
   (serializes (Data X P_left P_right) (inl (v ...)) (L cell ...))]

  [(serializes-fields (data-fields (Data X P_left P_right) right) (v ...) (cell ...))
   ------------------------------ "inr"
   (serializes (Data X P_left P_right) (inr (v ...)) (R cell ...))])

(define-judgment-form Shape
  #:mode (serializes-fields I I O)
  #:contract (serializes-fields P (v ...) S)

  [------------------------------ "nil"
   (serializes-fields () () ())]

  [(serializes A v (cell_1 ...))
   (serializes-fields (A_rest ...) (v_rest ...) (cell_2 ...))
   ------------------------------ "cons"
   (serializes-fields (A A_rest ...) (v v_rest ...) (cell_1 ... cell_2 ...))])

;; The outputs are the decoded value and the cells left unread.
(define-judgment-form Shape
  #:mode (consumes I I O O)
  #:contract (consumes A S v S)

  [------------------------------ "int"
   (consumes Int ((I n) cell ...) n (cell ...))]

  [(consumes-fields (data-fields (Data X P_left P_right) left) (cell ...)
                    (v ...) S_rest)
   ------------------------------ "inl"
   (consumes (Data X P_left P_right) (L cell ...) (inl (v ...)) S_rest)]

  [(consumes-fields (data-fields (Data X P_left P_right) right) (cell ...)
                    (v ...) S_rest)
   ------------------------------ "inr"
   (consumes (Data X P_left P_right) (R cell ...) (inr (v ...)) S_rest)])

;; Each field decides where the next one starts.
(define-judgment-form Shape
  #:mode (consumes-fields I I O O)
  #:contract (consumes-fields P S (v ...) S)

  [------------------------------ "nil"
   (consumes-fields () S () S)]

  [(consumes A S v S_middle)
   (consumes-fields (A_rest ...) S_middle (v_rest ...) S_out)
   ------------------------------ "cons"
   (consumes-fields (A A_rest ...) S (v v_rest ...) S_out)])

;; Consuming a whole pending protocol, discarding the values it decodes.  This
;; is what says a cursor's remaining obligations are satisfiable by the cells
;; still in front of it.
(define-judgment-form Shape
  #:mode (consumes-protocol I I O)
  #:contract (consumes-protocol P S S)
  [(consumes-fields P S_in (v ...) S_out)
   ------------------------------ "protocol"
   (consumes-protocol P S_in S_out)])

;; Encoding read as a function, for the places that want the cells directly.
;; Raises rather than returning a sentinel, so a mis-shaped value is loud.
(define (serialize shape value)
  (match (judgment-holds (serializes ,shape ,value S) S)
    [(list cells) cells]
    ['() (error 'serialize "~e does not have shape ~e" value shape)]
    [others (error 'serialize "ambiguous encoding: ~e" others)]))

(module+ test
  (define sample-tree
    (term (inr ((inl (1)) (inr ((inl (2)) (inl (3))))))))
  (define sample-store (term (R L (I 1) R L (I 2) L (I 3))))

  (check-equal? (serialize tree-shape sample-tree) sample-store)

  ;; Encoding is a partial function: at most one cell sequence per value.
  (check-equal?
   (length (judgment-holds (serializes ,tree-shape ,sample-tree S) S))
   1)

  ;; Adequacy: decoding an encoding gives the value back with nothing left.
  (check-equal?
   (judgment-holds (consumes ,tree-shape ,sample-store v ()) v)
   (list sample-tree))
  (check-equal?
   (judgment-holds (consumes Int ((I 5)) v ()) v)
   (list (term 5)))
  (check-equal?
   (judgment-holds (consumes (Data X (Int Int) ()) (L (I 1) (I 2)) v ()) v)
   (list (term (inl (1 2)))))

  ;; Decoding is a partial function too.
  (check-equal?
   (length (judgment-holds (consumes ,tree-shape ,sample-store v S) (v S)))
   1)

  ;; A value's encoding is a prefix: whatever follows is handed back unread.
  (check-equal?
   (judgment-holds (consumes ,tree-shape (L (I 4) R L (I 9)) v S) (v S))
   (list (list (term (inl (4))) (term (R L (I 9))))))

  (check-equal?
   (judgment-holds (consumes-protocol (Int Int) ((I 1) (I 2) L) S) S)
   (list (term (L))))

  ;; A list's nil is a lone tag.
  (check-equal? (serialize list-shape (term (inr (3 (inl ())))))
                (term (R (I 3) L)))

  ;; Cells that do not decode at the shape have no derivation at all.
  (check-false (judgment-holds (consumes Int (L) v S))))
