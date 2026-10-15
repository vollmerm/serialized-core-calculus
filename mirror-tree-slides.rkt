#lang slideshow

;; mirror-tree, animated one machine step per advance.
;;
;;   racket -l racket/base -e '(dynamic-require (quote slideshow/start) #f)' \
;;     -- mirror-tree-slides.rkt
;;
;; or open this file in DrRacket and run it, or use the `slideshow` launcher
;; where it starts.  Put `-x` before the file name to export one PDF page per
;; step instead.
;;
;; As in add1-tree-slides.rkt, the deck starts with the input finished and
;; about to be opened.  What differs is the lanes: besides the input and the
;; output, each node's left subtree gets a buffer of its own, filled by
;; `copy-tree`, then opened and read back after the right subtree is written.

(require "render.rkt"
         "animate.rkt"
         "examples.rkt")

(define mirror-film
  (run->film recursive-signatures (mirror-tree-program sample-tree)))

;; The state just before the input is opened.
(define start
  (sub1 (for/first ([s (in-list (film-scenes mirror-film))]
                    #:when (equal? (scene-rule s) "open"))
          (scene-index s))))

(slide
 #:title "mirror-tree"
 (para "Read a serialized tree and write it with every node's subtrees swapped."
       "Each advance is one machine step.")
 (para "The reader reaches a node's left subtree first, but the writer must"
       "put the right one there.  So the left subtree is copied into a buffer,"
       "the right subtree is mirrored into the output, and then the buffer is"
       "opened and mirrored after it.")
 (para "Each lane is one buffer.  A reader's cursor is under the next cell it"
       "will read; a writer's is under the empty slot it will fill next.")
 (para "Cursors are"
       (colorize (t "blue") reader-color) "for a live reader,"
       (colorize (t "red") writer-color) "for a live writer,"
       (colorize (t "orange") yielded-color) "while yielded, and"
       (colorize (t "grey") saved-color) "while held by a suspended caller.")
 (para "On the stack, a red scope is linear: it closes only once its writer is gone."))

(film-slides mirror-film #:from start)

;; `raco test` would otherwise run the slideshow.
(module test racket/base)
