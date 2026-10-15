#lang slideshow

;; add1-tree, animated one machine step per advance.
;;
;;   racket -l racket/base -e '(dynamic-require (quote slideshow/start) #f)' \
;;     -- add1-tree-slides.rkt
;;
;; or open this file in DrRacket and run it, or use the `slideshow` launcher
;; where it starts.  Put `-x` before the file name to export one PDF page per
;; step instead.
;;
;; The program first builds its input with explicit writes (see
;; `serialize-tree-term` in examples.rkt).  The deck starts just after that,
;; with the input finished and about to be opened, since the interesting part
;; is the traversal: a reader and a writer moving over two buffers in
;; lockstep, handed down through each recursive call and back up again.

(require "render.rkt"
         "animate.rkt"
         "examples.rkt")

(define add1-film
  (run->film recursive-signatures (add1-tree-program sample-tree)))

;; The state just before the input is opened.
(define start
  (sub1 (for/first ([s (in-list (film-scenes add1-film))]
                    #:when (equal? (scene-rule s) "open"))
          (scene-index s))))

(slide
 #:title "add1-tree"
 (para "Read a serialized tree and write a copy with every leaf incremented."
       "Each advance is one machine step.")
 (para "Each lane is one buffer.  A reader's cursor is under the next cell it"
       "will read; a writer's is under the empty slot it will fill next.")
 (para "Cursors are"
       (colorize (t "blue") reader-color) "for a live reader,"
       (colorize (t "red") writer-color) "for a live writer,"
       (colorize (t "orange") yielded-color) "while yielded, and"
       (colorize (t "grey") saved-color) "while held by a suspended caller.")
 (para "On the stack, a red scope is linear: it closes only once its writer is gone."))

(film-slides add1-film #:from start)

;; `raco test` would otherwise run the slideshow.
(module test racket/base)
