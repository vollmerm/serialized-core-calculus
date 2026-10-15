#lang racket

;; Playing a film (see render.rkt) as a slideshow.
;;
;; Each machine step is one advance: the step animates from the state before
;; it to the state after it, and then waits.  Backing up goes one state back.
;; Nothing here depends on which program is running; add1-tree-slides.rkt is
;; one deck built from it.
;;
;; These functions add slides, so they only make sense inside a slideshow
;; program, run with `slideshow <file>` or from DrRacket.

(require pict
         slideshow/base
         slideshow/play
         "render.rkt")

(provide film-slides)

;; Each frame is scaled to fill as much of the slide as it can.
(define (fit p)
  (scale p (min (/ client-w (pict-width p)) (/ client-h (pict-height p)))))

;; Slides for the states from `from` to the end of the film.  `steps` frames
;; of `delay` seconds each make one machine step's animation.
(define (film-slides a-film
                     #:from [from 0]
                     #:steps [steps 10]
                     #:delay [delay 0.03])
  (slide #:layout 'center (fit (film-frame a-film from)))
  (for ([i (in-range (add1 from) (film-length a-film))])
    (play-n (lambda (n) (fit (film-transition a-film i n)))
            #:steps steps
            #:delay delay
            #:skip-first? #t
            #:layout 'center)))

;; Requiring this module outside a slideshow is harmless, but there is
;; nothing to test without one.
(module test racket/base)
