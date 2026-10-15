#lang racket

;; Worked programs.
;;
;; `build-seven` is the smallest complete program: make a writer, write one
;; integer, finish.  The two traversals after it are the point of the whole
;; design -- recursive functions over serialized trees that never materialize
;; a tree, never store an offset, and never copy a subtree.
;;
;; `sum-tree` reads and returns an integer.  `add1-tree` reads and writes at
;; the same time, which is where the affine/linear split earns its keep: the
;; reader may be abandoned at any point, the writer may not.
;;
;; `mirror-tree` is the exception to "never copy": its output order differs
;; from its input order, so it stages each left subtree in a buffer of its own.

(require redex/reduction-semantics
         rackunit
         "shape.rkt"
         "layout.rkt"
         "protocol.rkt"
         "capability.rkt"
         "syntax.rkt"
         "match.rkt"
         "typing.rkt"
         "machine.rkt")

(provide (all-defined-out))

;; Tree = data X. leaf(Int) | node(X, X)
(define Tree tree-shape)

(define (leaf n) (term (inl (,n))))
(define (node lhs rhs) (term (inr (,lhs ,rhs))))

(define sample-tree (node (leaf 1) (node (leaf 2) (leaf 3))))

(define build-seven
  (term (let (bind () (w)) (new Int)
          (let (bind () (w2)) (write-int w 7)
            (finish w2)))))

;; ---------------------------------------------------------------------------
;; Building a tree, as a term
;;
;; The writes are emitted explicitly so the examples stay closed: nothing is
;; smuggled in through a starting environment, and the whole program can be
;; handed to `closed-term-typing`.
;; ---------------------------------------------------------------------------

(define (build-tree-writes value current k)
  (define counter (box 0))
  (define (next!)
    (set-box! counter (add1 (unbox counter)))
    (string->symbol (format "w~a" (unbox counter))))
  (let build ([value value] [current current] [k k])
    (match value
      [`(inl (,n))
       (define tagged (next!))
       (define written (next!))
       (term (let (bind () (,tagged)) (write-left ,current)
               (let (bind () (,written)) (write-int ,tagged ,n)
                 ,(k written))))]
      [`(inr (,lhs ,rhs))
       (define tagged (next!))
       ;; The left subtree's writer is what the right subtree continues from,
       ;; which is the whole reason no offset is needed.
       (term (let (bind () (,tagged)) (write-right ,current)
               ,(build lhs tagged
                       (lambda (after-left) (build rhs after-left k)))))])))

;; Builds `value`, finishes the writer, and hands the result to `k` as an
;; ordinary variable.
(define (serialize-tree-term value k)
  (term (let (bind (s) ())
             (let (bind () (w0)) (new ,Tree)
               ,(build-tree-writes value 'w0
                                   (lambda (final) (term (finish ,final)))))
          ,(k 's))))

;; ---------------------------------------------------------------------------
;; sum-tree: read a tree, return the sum of its leaves.
;;
;; The reader's row ends in its frame, `(tvar 0)`.  It takes a reader positioned
;; at a tree followed by *whatever the caller had lined up after it*, and
;; returns a reader positioned at exactly that remainder.
;;
;; That is what makes the two recursive calls work.  At a node the reader is
;; positioned at `(Tree Tree)`; the first call matches `Tree` against the
;; left subtree and binds the frame to the right one, so the reader it hands
;; back is already at the sibling.  The second call then finds a closed tail.
;; ---------------------------------------------------------------------------

(define sum-tree-signature
  (term (sig ()                                  ; ordinary inputs
             ((Read (row (,Tree) (tvar 0))))     ; resource inputs
             (Int)                               ; ordinary outputs
             ((Read (row () (tvar 0)))))))       ; resource outputs

(define sum-tree-definition
  (term (def ,sum-tree-signature
          (bind () (rd))
          (switch rd
            (left rd1 (read-int rd1))
            (right rd1
              (let (bind (lsum) (rdl)) (call sum-tree () (rd1))
                (let (bind (rsum) (rdr)) (call sum-tree () (rdl))
                  (let (bind (total) ()) (arith add lsum rsum)
                    (return (total) (rdr))))))))))

;; ---------------------------------------------------------------------------
;; add1-tree: read a tree and write the same tree with every leaf incremented.
;;
;; Two frames, one for the reader and one for the writer, so a
;; recursive call hands both capabilities back positioned after the subtree it
;; processed.  The reader and the writer advance in lockstep without either
;; one knowing where the other is.
;; ---------------------------------------------------------------------------

(define add1-tree-signature
  (term (sig ()
             ((Read (row (,Tree) (tvar 0)))
              (Write (row (,Tree) (tvar 1)) ,Tree))
             ()
             ((Read (row () (tvar 0)))
              (Write (row () (tvar 1)) ,Tree)))))

(define add1-tree-definition
  (term (def ,add1-tree-signature
          (bind () (rd wt))
          (switch rd
            (left rd1
              (let (bind (v) (rd2)) (read-int rd1)
                (let (bind () (wt1)) (write-left wt)
                  (let (bind (v1) ()) (arith add v 1)
                    (let (bind () (wt2)) (write-int wt1 v1)
                      (return () (rd2 wt2)))))))
            (right rd1
              (let (bind () (wt1)) (write-right wt)
                (let (bind () (rdl wtl)) (call add1-tree () (rd1 wt1))
                  (call add1-tree () (rdl wtl)))))))))

;; ---------------------------------------------------------------------------
;; build-tree: write a complete tree of the given depth, with 1 at every leaf.
;;
;; The recursion is on an ordinary integer, and the branch is on a comparison
;; rather than a tag in the store.  As in the host-level `build-tree-writes`
;; above, the left subtree's returned writer is where the right one starts.
;; ---------------------------------------------------------------------------

(define build-tree-signature
  (term (sig (Int)
             ((Write (row (,Tree) (tvar 0)) ,Tree))
             ()
             ((Write (row () (tvar 0)) ,Tree)))))

(define build-tree-definition
  (term (def ,build-tree-signature
          (bind (n) (wt))
          (if le n 0
            (let (bind () (wt1)) (write-left wt)
              (write-int wt1 1))
            (let (bind () (wt1)) (write-right wt)
              (let (bind (m) ()) (arith sub n 1)
                (let (bind () (wtl)) (call build-tree (m) (wt1))
                  (call build-tree (m) (wtl)))))))))

;; ---------------------------------------------------------------------------
;; sum-list: sum a list whose nil carries no payload.
;;
;; Nil has no fields, so in the nil branch the reader is positioned at just the
;; tail, and the branch hands it straight back.
;; ---------------------------------------------------------------------------

(define sum-list-signature
  (term (sig ()
             ((Read (row (,list-shape) (tvar 0))))
             (Int)
             ((Read (row () (tvar 0)))))))

(define sum-list-definition
  (term (def ,sum-list-signature
          (bind () (rd))
          (switch rd
            (left rd1 (return (0) (rd1)))
            (right rd1
              (let (bind (v) (rd2)) (read-int rd1)
                (let (bind (rest) (rd3)) (call sum-list () (rd2))
                  (let (bind (total) ()) (arith add v rest)
                    (return (total) (rd3))))))))))

;; ---------------------------------------------------------------------------
;; mirror-tree: read a tree and write it with every node's subtrees swapped.
;;
;; The reader meets a node's left subtree first, but the writer has to put the
;; mirrored right subtree there.  So the left subtree goes into a buffer of
;; its own, the right subtree is mirrored straight into the writer, and then
;; the buffer is opened and mirrored after it.
;;
;; `copy-tree` is `add1-tree` without the increment.  Copying the left subtree
;; into a buffer hands back two things at once -- the finished buffer and the
;; reader positioned after the subtree -- and a `let` names both.
;;
;; Each node copies its left subtree once, so the traversal costs
;; O(size * depth) rather than O(size).
;; ---------------------------------------------------------------------------

(define copy-tree-definition
  (term (def ,add1-tree-signature
          (bind () (rd wt))
          (switch rd
            (left rd1
              (let (bind (v) (rd2)) (read-int rd1)
                (let (bind () (wt1)) (write-left wt)
                  (let (bind () (wt2)) (write-int wt1 v)
                    (return () (rd2 wt2))))))
            (right rd1
              (let (bind () (wt1)) (write-right wt)
                (let (bind () (rdl wtl)) (call copy-tree () (rd1 wt1))
                  (call copy-tree () (rdl wtl)))))))))

;; The same signature as add1-tree: the traversal is still one reader and one
;; writer in, both handed back past the tree.  The buffer is opened on a
;; closed row, so the second call binds the reader's frame to `closed`.
(define mirror-tree-definition
  (term (def ,add1-tree-signature
          (bind () (rd wt))
          (switch rd
            (left rd1
              (let (bind (v) (rd2)) (read-int rd1)
                (let (bind () (wt1)) (write-left wt)
                  (let (bind () (wt2)) (write-int wt1 v)
                    (return () (rd2 wt2))))))
            (right rd1
              (let (bind () (wt1)) (write-right wt)
                (let (bind (s) (rdl))
                     (let (bind () (buf)) (new ,Tree)
                       (let (bind () (rd2 buf2)) (call copy-tree () (rd1 buf))
                         (let (bind (s) ()) (finish buf2)
                           (return (s) (rd2)))))
                  (let (bind () (rdr wtr)) (call mirror-tree () (rdl wt1))
                    (let (bind () (tmp)) (open s)
                      (let (bind () (tmp2 wt3)) (call mirror-tree () (tmp wtr))
                        (return () (rdr wt3))))))))))))

(define recursive-signatures
  (term ((sum-tree ,sum-tree-definition)
         (add1-tree ,add1-tree-definition)
         (build-tree ,build-tree-definition)
         (sum-list ,sum-list-definition)
         (copy-tree ,copy-tree-definition)
         (mirror-tree ,mirror-tree-definition))))

;; ---------------------------------------------------------------------------
;; Whole programs
;; ---------------------------------------------------------------------------

(define (sum-tree-program value)
  (serialize-tree-term
   value
   (lambda (serialized)
     (term (let (bind () (rd)) (open ,serialized)
             (let (bind (total) (rd2)) (call sum-tree () (rd))
               (return (total) ())))))))

(define (build-sum-program depth)
  (term (let (bind (s) ())
             (let (bind () (wt)) (new ,Tree)
               (let (bind () (wt2)) (call build-tree (,depth) (wt))
                 (finish wt2)))
          (let (bind () (rd)) (open s)
            (let (bind (total) (rd2)) (call sum-tree () (rd))
              (return (total) ()))))))

;; Write a list of integers with the writer operations, then sum it.
(define (sum-list-program numbers)
  (define (writes current k)
    (let loop ([numbers numbers] [current current] [counter 0])
      (define tagged (string->symbol (format "l~a" counter)))
      (define written (string->symbol (format "l~a" (add1 counter))))
      (match numbers
        ['() (term (let (bind () (,tagged)) (write-left ,current) ,(k tagged)))]
        [(cons n rest)
         (term (let (bind () (,tagged)) (write-right ,current)
                 (let (bind () (,written)) (write-int ,tagged ,n)
                   ,(loop rest written (+ counter 2)))))])))
  (term (let (bind (s) ())
             (let (bind () (l)) (new ,list-shape)
               ,(writes 'l (lambda (final) (term (finish ,final)))))
          (let (bind () (rd)) (open s)
            (let (bind (total) (rd2)) (call sum-list () (rd))
              (return (total) ()))))))

(define (list-value numbers)
  (foldr (lambda (n rest) (term (inr (,n ,rest))))
         (term (inl ()))
         numbers))

(define (add1-tree-program value)
  (serialize-tree-term
   value
   (lambda (serialized)
     (term (let (bind () (rd)) (open ,serialized)
             (let (bind () (wt)) (new ,Tree)
               (let (bind () (rd2 wt2)) (call add1-tree () (rd wt))
                 (finish wt2))))))))

(define (mirror-tree-program value)
  (serialize-tree-term
   value
   (lambda (serialized)
     (term (let (bind () (rd)) (open ,serialized)
             (let (bind () (wt)) (new ,Tree)
               (let (bind () (rd2 wt2)) (call mirror-tree () (rd wt))
                 (finish wt2))))))))

;; Ordinary semantics, to check the serialized programs against.
(define (tree-sum value)
  (match value
    [`(inl (,n)) n]
    [`(inr (,lhs ,rhs)) (+ (tree-sum lhs) (tree-sum rhs))]))

(define (tree-add1 value)
  (match value
    [`(inl (,n)) (leaf (add1 n))]
    [`(inr (,lhs ,rhs)) (node (tree-add1 lhs) (tree-add1 rhs))]))

(define (tree-mirror value)
  (match value
    [`(inl (,n)) value]
    [`(inr (,lhs ,rhs)) (node (tree-mirror rhs) (tree-mirror lhs))]))

(module+ test
  ;; The environment checks against itself, which is what admits the recursive
  ;; calls.
  (check-true (signature-env-ok? recursive-signatures))

  (check-equal? (type-of (term ()) build-seven)
                (list (term (bundle ((Ser Int)) ()))))
  (check-equal? (result-of (run-term (term ()) build-seven))
                (term (ser Int ((I 7)))))

  ;; Building a tree by hand produces the same cells as the encoding relation.
  (define built
    (run-term (term ())
              (serialize-tree-term sample-tree (lambda (s) (term (return (,s) ()))))))
  (check-equal? (result-of built)
                (term (ser ,Tree ,(serialize Tree sample-tree))))

  ;; sum-tree checks, and agrees with the ordinary semantics.
  (check-equal? (type-of recursive-signatures (sum-tree-program sample-tree))
                (list (term (bundle (Int) ()))))
  (check-equal? (result-of (run-term recursive-signatures
                                     (sum-tree-program sample-tree)))
                (tree-sum sample-tree))

  ;; add1-tree checks, and produces exactly the encoding of the incremented
  ;; tree -- cell for cell, not merely a value that decodes the same way.
  (check-equal? (type-of recursive-signatures (add1-tree-program sample-tree))
                (list (term (bundle ((Ser ,Tree)) ()))))
  (check-equal? (result-of (run-term recursive-signatures
                                     (add1-tree-program sample-tree)))
                (term (ser ,Tree ,(serialize Tree (tree-add1 sample-tree)))))

  ;; mirror-tree checks, and produces exactly the encoding of the mirrored
  ;; tree, using a buffer for each left subtree along the way.
  (check-equal? (type-of recursive-signatures (mirror-tree-program sample-tree))
                (list (term (bundle ((Ser ,Tree)) ()))))
  (for ([value (list (leaf 7)
                     sample-tree
                     (node (node (leaf 1) (leaf 2))
                           (node (leaf 3) (node (leaf 4) (leaf 5)))))])
    (check-equal? (result-of (run-term recursive-signatures
                                       (mirror-tree-program value)))
                  (term (ser ,Tree ,(serialize Tree (tree-mirror value))))))

  ;; build-tree makes the tree itself, from an integer; summing it counts the
  ;; leaves of a complete tree.
  (check-equal? (type-of recursive-signatures (build-sum-program 3))
                (list (term (bundle (Int) ()))))
  (for ([depth (in-range 0 5)])
    (check-equal? (result-of (run-term recursive-signatures
                                       (build-sum-program depth)))
                  (expt 2 depth)))

  ;; sum-list checks, and agrees with the ordinary sum; the list it reads is
  ;; the encoding of the list, nil being a lone tag.
  (check-equal? (type-of recursive-signatures (sum-list-program '(3 4)))
                (list (term (bundle (Int) ()))))
  (for ([numbers (list '() '(5) '(3 4) '(1 -2 3 -4 5))])
    (check-equal? (result-of (run-term recursive-signatures
                                       (sum-list-program numbers)))
                  (apply + numbers)))
  (check-equal? (serialize list-shape (list-value '(3 4)))
                (term (R (I 3) R (I 4) L)))

  ;; Reading a leaf where a node is expected is not a type error -- the tag is
  ;; only known at run time -- so both branches must be well typed, and the
  ;; run takes whichever the store selects.
  (check-equal? (result-of (run-term recursive-signatures
                                     (sum-tree-program (leaf 42))))
                42))
