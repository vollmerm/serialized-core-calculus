#lang racket

;; Ways to look at a program running, or at why it type checks.
;;
;; Nothing here is part of the model.  These are entry points into the
;; graphical tools and a plain-text step log, kept apart so that the model
;; itself has no dependency on a display.

(require racket/lazy-require
         redex/reduction-semantics
         "shape.rkt"
         "protocol.rkt"
         "capability.rkt"
         "syntax.rkt"
         "typing.rkt"
         "machine.rkt")

;; Loaded only when one of the graphical entry points is actually called, so
;; requiring this module on a machine with no display is harmless.
(lazy-require [redex/gui (traces stepper show-derivations)])

(provide trace-program step-program show-typing
         summarize-state run-log)

;; ---------------------------------------------------------------------------
;; Graphical
;; ---------------------------------------------------------------------------

;; Draw the whole reduction graph of a program.  Every node is a machine
;; state; every edge is labelled with the rule that fired.
(define (trace-program sigma expression)
  (traces machine-step (term (initial ,sigma ,expression))))

;; Step a program forwards and backwards by hand.
(define (step-program sigma expression)
  (stepper machine-step (term (initial ,sigma ,expression))))

;; Draw the typing derivation of a closed program.
(define (show-typing sigma expression)
  (define derivations (typing-derivations sigma expression))
  (if (null? derivations)
      (error 'show-typing "term does not type check")
      (show-derivations derivations)))

;; ---------------------------------------------------------------------------
;; Textual
;;
;; A machine state carries whole stores and whole continuations, which is more
;; than is useful to read at each step.  `summarize-state` keeps the part that
;; changes: which rule applies next, what each capability is looking at, and
;; how the scopes are nested.
;; ---------------------------------------------------------------------------

(define (summarize-control control)
  (match control
    [`(ctl-term (,head . ,_)) head]
    [`(ctl-bundle ,values ,resources)
     `(bundle ,(map summarize-value values)
              ,(map summarize-resource resources))]))

(define (summarize-value value)
  (match value
    [(? integer? n) n]
    [`(ser ,shape ,cells) `(ser ,(length cells))]))

(define (summarize-resource resource)
  (match resource
    [`(reader ,store ,pending ,position ,endpoint)
     `(reader ,position / ,endpoint owing ,(length pending))]
    [`(writer ,cells ,pending ,shape)
     `(writer ,(length cells) cells owing ,(length pending))]))

(define (summarize-frame frame)
  (match frame
    [`(frame-let (bind ,xs ,rs) ,_ ,_) `(let ,@xs ,@rs)]
    [`(frame-scope ,_ ,names) `(scope ,@names)]
    [`(frame-call ,_ ,_) 'call]))

;; The stack is shown as its depth plus its top few frames; the rest is
;; scopes waiting to be popped and rarely the interesting part.
(define stack-shown 3)

(define (summarize-stack stack)
  (define top (map summarize-frame (take stack (min stack-shown (length stack)))))
  (if (> (length stack) stack-shown)
      `(,(length stack) : ,@top ...)
      `(,(length stack) : ,@top)))

(define (summarize-state state)
  (match state
    [`(machine ,_ (config ,control ,_ ,resources ,stack))
     (list (summarize-control control)
           (for/list ([binding (in-list resources)])
             (list (first binding) (summarize-resource (second binding))))
           (summarize-stack stack))]))

;; Run a program, printing one line per step: the rule that fired and the
;; state it produced.  Ends with `final` or `STUCK`, which is the interesting
;; distinction.
(define (run-log sigma expression #:fuel [fuel 500])
  (let loop ([state (term (initial ,sigma ,expression))] [step 0])
    (define tagged (apply-reduction-relation/tag-with-names machine-step state))
    (cond
      [(null? tagged)
       (printf "~a ~a\n" (~a step #:min-width 4)
               (if (term (final? ,state)) "final" "STUCK"))
       state]
      [(= step fuel)
       (printf "~a out of fuel\n" (~a step #:min-width 4))
       state]
      [else
       (define name (first (first tagged)))
       (define next (second (first tagged)))
       (match-define (list control resources stack) (summarize-state next))
       (printf "~a ~a ~a ~a ~a\n"
               (~a step #:min-width 4)
               (~a name #:min-width 14)
               (~a control #:min-width 14)
               (~a resources #:min-width 34)
               stack)
       (when (pair? (cdr tagged))
         (printf "     (also: ~a)\n" (map first (cdr tagged))))
       (loop next (add1 step))])))
