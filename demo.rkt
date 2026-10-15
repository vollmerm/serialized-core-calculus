#lang racket

;; Demos: named entry points onto the worked examples in examples.rkt,
;; through the tools in explore.rkt.
;;
;; Each example program gets four entry points, one per tool in explore.rkt:
;;
;;   - `-log`    prints one line per machine step to the terminal, via
;;               `run-log`.  Needs no display.
;;   - `-trace`  draws the whole reduction graph, via `trace-program`.
;;   - `-step`   opens a stepper to walk the same reduction by hand, via
;;               `step-program`.
;;   - `-typing` draws the typing derivation, via `show-typing`.
;;
;; The `-trace`, `-step`, and `-typing` entry points open a DrRacket window
;; and so only make sense at the DrRacket REPL. The `-log` entry points are
;; plain text and work from any terminal, which is also what `run-all-demos`
;; below uses to give a quick sanity check that every worked example still
;; runs to the answer examples.rkt's tests expect.
;;
;; From a REPL:
;;
;;   (require "demo.rkt")
;;   (build-seven-log)
;;   (sum-tree-trace)
;;   (add1-tree-typing (leaf 5))
;;
;; From a terminal, `racket demo.rkt` runs every `-log` entry point in turn.

(require redex/reduction-semantics
         "examples.rkt"
         "typing.rkt"
         "machine.rkt"
         "explore.rkt")

(provide build-seven-log build-seven-trace build-seven-step build-seven-typing
         sum-tree-log sum-tree-trace sum-tree-step sum-tree-typing
         add1-tree-log add1-tree-trace add1-tree-step add1-tree-typing
         run-all-demos)

;; ---------------------------------------------------------------------------
;; build-seven: the smallest complete program -- make a writer, write one
;; integer, finish.  No signature environment is needed.
;; ---------------------------------------------------------------------------

(define (build-seven-log) (run-log (term ()) build-seven))
(define (build-seven-trace) (trace-program (term ()) build-seven))
(define (build-seven-step) (step-program (term ()) build-seven))
(define (build-seven-typing) (show-typing (term ()) build-seven))

;; ---------------------------------------------------------------------------
;; sum-tree: read a serialized tree, return the sum of its leaves.  Defaults
;; to sample-tree, a node with three leaves, but any tree value works --
;; `(leaf 42)` below is a one-branch run with no recursive call at all.
;; ---------------------------------------------------------------------------

(define (sum-tree-log [value sample-tree])
  (run-log recursive-signatures (sum-tree-program value)))
(define (sum-tree-trace [value sample-tree])
  (trace-program recursive-signatures (sum-tree-program value)))
(define (sum-tree-step [value sample-tree])
  (step-program recursive-signatures (sum-tree-program value)))
(define (sum-tree-typing [value sample-tree])
  (show-typing recursive-signatures (sum-tree-program value)))

;; ---------------------------------------------------------------------------
;; add1-tree: read a serialized tree, write the same tree with every leaf
;; incremented.  Reader and writer steps interleave, which is the
;; interesting part to watch in the log or the trace.
;; ---------------------------------------------------------------------------

(define (add1-tree-log [value sample-tree])
  (run-log recursive-signatures (add1-tree-program value)))
(define (add1-tree-trace [value sample-tree])
  (trace-program recursive-signatures (add1-tree-program value)))
(define (add1-tree-step [value sample-tree])
  (step-program recursive-signatures (add1-tree-program value)))
(define (add1-tree-typing [value sample-tree])
  (show-typing recursive-signatures (add1-tree-program value)))

;; ---------------------------------------------------------------------------
;; Running everything from a terminal
;; ---------------------------------------------------------------------------

(define (run-all-demos)
  (define (section title thunk)
    (printf "\n== ~a ==\n" title)
    (thunk)
    (void))
  (section "build-seven" build-seven-log)
  (section "sum-tree, a single leaf" (lambda () (sum-tree-log (leaf 42))))
  (section "sum-tree, sample-tree" (lambda () (sum-tree-log sample-tree)))
  (section "add1-tree, sample-tree" (lambda () (add1-tree-log sample-tree)))
  (void))

(module+ main
  (run-all-demos))

(module+ test
  (require rackunit racket/port)

  ;; Each `-log` entry point actually reaches a final state without needing a
  ;; display -- the same guarantee examples.rkt checks with run-term, here
  ;; exercised through the logging path instead.
  (define (silently thunk)
    (parameterize ([current-output-port (open-output-nowhere)])
      (thunk)))

  (check-true (term (final? ,(silently build-seven-log))))
  (check-true (term (final? ,(silently (lambda () (sum-tree-log (leaf 42)))))))
  (check-true (term (final? ,(silently sum-tree-log))))
  (check-true (term (final? ,(silently add1-tree-log)))))
