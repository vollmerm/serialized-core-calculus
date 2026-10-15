#lang racket

;; Drawing machine runs as pictures.
;;
;; Nothing here is part of the model, and nothing here needs a display: every
;; drawing is a pict, which can be saved to a PNG or PDF, dropped into a
;; slideshow (see animate.rkt), or shown at the DrRacket REPL.
;;
;; A run is turned into a *film*: one scene per machine state.  The hard part
;; is deciding what stays put from one scene to the next.  The machine renames
;; a capability every time it advances one, and the old name is gone in the
;; same step the new one appears, so names cannot say "this is the same buffer
;; as before".  The film instead tracks *lanes*, one per buffer:
;;
;;   - A reader belongs to the lane for its store and endpoint.  Reading never
;;     changes either, so every successor of a reader lands in the same lane,
;;     and the cursor visibly moves along it.
;;   - A writer belongs to the lane whose last writer's cells are a prefix of
;;     its own, among lanes that held a writer in the previous state.  Writing
;;     only appends, so a successor always extends its predecessor.
;;
;; A lane is drawn as the row of cells, with one cursor under it per capability
;; on it.  A reader's cursor sits under the next cell it will read; a writer's
;; sits under the empty slot it will write next.  Readers and writers are drawn
;; on the same grid, so a traversal that reads and writes in lockstep, like
;; add1-tree, shows the two cursors moving together.
;;
;; A capability is not always in the current resource environment.  It can be
;; in flight inside a yielded bundle, or held by a caller suspended on a call
;; frame.  Those are still drawn, in a different colour, since the lane would
;; otherwise go blank in the middle of every call.

(require pict
         racket/draw
         redex/reduction-semantics
         "shape.rkt"
         "machine.rkt")

(provide shape-abbreviations
         (struct-out film)
         (struct-out scene)
         run->film
         film-length
         film-frame
         film-transition
         film-lane-cells
         state->pict
         save-pict
         reader-color writer-color yielded-color saved-color)

;; ---------------------------------------------------------------------------
;; Running
;; ---------------------------------------------------------------------------

;; One scene per machine state.  `rule` is the name of the rule that produced
;; the state, or #f for the initial one.  `views` has one entry per lane of the
;; whole film, in the same order in every scene, so lanes never move.
(struct scene (index rule state views) #:transparent)
(struct film (scenes lane-count max-cells) #:transparent)

(define (film-length a-film) (length (film-scenes a-film)))

;; The whole run, as (rule . state) pairs.  Like `run`, refuses a machine that
;; offers two steps, since a film has no way to show a branch.
(define (trace-run sigma expression fuel)
  (let loop ([state (term (initial ,sigma ,expression))]
             [rule #f]
             [remaining fuel]
             [acc '()])
    (define acc* (cons (cons rule state) acc))
    (match (apply-reduction-relation/tag-with-names machine-step state)
      ['() (reverse acc*)]
      [(list (list name next))
       (when (zero? remaining)
         (error 'run->film "out of fuel after ~a steps" fuel))
       (loop next name (sub1 remaining) acc*)]
      [nexts (error 'run->film "machine offered two steps: ~e" (map first nexts))])))

(define (run->film sigma expression #:fuel [fuel 2000])
  (define steps (trace-run sigma expression fuel))
  (define-values (lanes assignments) (assign-lanes (map cdr steps)))
  (define views (lane-views lanes assignments))
  (define scenes
    (for/list ([step (in-list steps)] [view (in-list views)] [i (in-naturals)])
      (scene i (car step) (cdr step) view)))
  (define max-cells
    (for*/fold ([widest 1]) ([view (in-list views)] [v (in-list view)])
      (max widest (length (view-cells v)))))
  (film scenes (length lanes) max-cells))

;; ---------------------------------------------------------------------------
;; Where capabilities live
;; ---------------------------------------------------------------------------

;; `place` is `live` (in the resource environment), `yielded` (in a bundle on
;; its way back to a caller; it has no name), or `saved` (held by a caller that
;; is suspended on a call frame).
(struct occ (name cap place) #:transparent)

(define (state-occurrences state)
  (match-define `(machine ,_ (config ,control ,_ ,resources ,stack)) state)
  (append
   (for/list ([binding (in-list resources)])
     (occ (first binding) (second binding) 'live))
   (match control
     [`(ctl-bundle ,_ ,caps) (for/list ([cap (in-list caps)]) (occ #f cap 'yielded))]
     [_ '()])
   (for*/list ([frame (in-list stack)]
               #:when (eq? (first frame) 'frame-call)
               [binding (in-list (third frame))])
     (occ (first binding) (second binding) 'saved))))

(define (cap-kind cap) (if (eq? (first cap) 'reader) 'reader 'writer))
(define (cap-cells cap) (second cap))
(define (cap-pending cap) (third cap))

;; ---------------------------------------------------------------------------
;; Lanes
;; ---------------------------------------------------------------------------

;; `key` is (store endpoint) for a reader lane and the result shape for a
;; writer lane.  `last` is the cells of the writer most recently seen on it.
(struct lane (id kind key [last #:mutable]))

(define (prefix? short long)
  (and (<= (length short) (length long))
       (equal? short (take long (length short)))))

;; Returns the lanes in creation order, and for each state a list of
;; (lane-id . occ).
(define (assign-lanes states)
  (define lanes '())
  (define (new-lane! kind key cells)
    (define fresh (lane (length lanes) kind key cells))
    (set! lanes (append lanes (list fresh)))
    fresh)
  (define-values (_ assignments)
    (for/fold ([previous (seteqv)] [acc '()]) ([state (in-list states)])
      (define claimed (mutable-seteqv))
      (define assigned
        (for/list ([o (in-list (state-occurrences state))])
          (define the-lane
            (match (occ-cap o)
              [`(reader ,cells ,_ ,_ ,end)
               (define key (list cells end))
               (or (findf (lambda (l) (and (eq? (lane-kind l) 'reader)
                                           (equal? (lane-key l) key)))
                          lanes)
                   (new-lane! 'reader key cells))]
              ;; A writer can only continue a lane that held a writer a
              ;; moment ago: writers are linear, so a lane that went empty
              ;; was finished and cannot come back.
              [`(writer ,cells ,_ ,shape)
               (define candidates
                 (filter (lambda (l)
                           (and (eq? (lane-kind l) 'writer)
                                (equal? (lane-key l) shape)
                                (set-member? previous (lane-id l))
                                (not (set-member? claimed (lane-id l)))
                                (prefix? (lane-last l) cells)))
                         lanes))
               (define chosen
                 (if (null? candidates)
                     (new-lane! 'writer shape cells)
                     (argmax (lambda (l) (length (lane-last l))) candidates)))
               (set-add! claimed (lane-id chosen))
               (set-lane-last! chosen cells)
               chosen]))
          (cons (lane-id the-lane) o)))
      (values (for/seteqv ([a (in-list assigned)]) (car a))
              (cons assigned acc))))
  (values lanes (reverse assignments)))

;; What one lane looks like in one state.  `status` is `unborn` (not created
;; yet), `present` (some capability is on it), or `gone` (it had one and no
;; longer does); `note` says why a lane is gone.
(struct view (kind status cells occs note) #:transparent)

(define (lane-views lanes assignments)
  (define last-cells (make-hasheqv))
  (define last-pending (make-hasheqv))
  (for/list ([assigned (in-list assignments)])
    (for/list ([l (in-list lanes)])
      (define id (lane-id l))
      (define occs (for/list ([a (in-list assigned)] #:when (= (car a) id)) (cdr a)))
      (cond
        [(pair? occs)
         (define cap (occ-cap (first occs)))
         (hash-set! last-cells id (cap-cells cap))
         (hash-set! last-pending id (cap-pending cap))
         (view (lane-kind l) 'present (cap-cells cap) occs #f)]
        [(hash-ref last-cells id #f)
         => (lambda (cells)
              (define note
                (cond [(eq? (lane-kind l) 'reader) "dropped"]
                      [(null? (hash-ref last-pending id)) "finished"]
                      [else "abandoned"]))
              (view (lane-kind l) 'gone cells '() note))]
        [else (view (lane-kind l) 'unborn '() '() #f)]))))

;; The cells last seen on each lane, for checking a film against the model.
(define (film-lane-cells a-film)
  (for/list ([v (in-list (scene-views (last (film-scenes a-film))))])
    (view-cells v)))

;; ---------------------------------------------------------------------------
;; Text
;; ---------------------------------------------------------------------------

;; Shapes spelled out in full are unreadable after one unfolding, so any
;; subterm equal to one of these is printed as its name.
(define shape-abbreviations
  (make-parameter (list (cons tree-shape 'Tree) (cons list-shape 'List))))

(define (abbreviate-shapes t)
  (cond [(assoc t (shape-abbreviations)) => cdr]
        [(pair? t) (map abbreviate-shapes t)]
        [else t]))

(define (term-depth t)
  (if (pair? t) (add1 (apply max 0 (map term-depth t))) 0))

(define expression-heads
  '(return let arith if read-int switch write-int write-left write-right
    open new finish call))

;; A term's head and its small arguments; subexpressions, which are the
;; continuations and branches, become an ellipsis.
(define (abbreviate-term e)
  (define (hidden? a)
    (or (> (term-depth a) 2)
        (and (pair? a) (memq (car a) expression-heads))))
  (match (abbreviate-shapes e)
    [(cons head args)
     (cons head (for/list ([a (in-list args)]) (if (hidden? a) '… a)))]
    [atom atom]))

(define (shape->string shape) (~a (abbreviate-shapes shape)))

(define (protocol->string pending)
  (if (null? pending)
      "nothing"
      (string-join (map shape->string pending) " · ")))

(define (value->string rv)
  (match rv
    [(? integer? n) (~a n)]
    [`(ser ,shape ,cells) (format "ser ~a [~a cells]" (shape->string shape) (length cells))]))

(define (control->string control)
  (match control
    [`(ctl-term ,e) (~a (abbreviate-term e))]
    [`(ctl-bundle ,values ,caps)
     (format "bundle  (~a)  +  ~a capabilit~a"
             (string-join (map value->string values) " ")
             (length caps) (if (= (length caps) 1) "y" "ies"))]))

(define (cell->string cell)
  (match cell ['L "L"] ['R "R"] [`(I ,n) (~a n)]))

(define rule-blurbs
  (hash "return"       "hand values and capabilities on to the next frame"
        "let"          "run the right-hand side first; the body waits on a let frame"
        "arith"        "compute an integer"
        "if-true"      "the comparison holds: take the first branch"
        "if-false"     "the comparison fails: take the second branch"
        "read-int"     "read the integer under the cursor, and produce the reader one cell on"
        "switch-left"  "the tag under the cursor is L: take the left branch, one cell on"
        "switch-right" "the tag under the cursor is R: take the right branch, one cell on"
        "write-int"    "append an integer, and produce the writer's successor"
        "write-left"   "append an L tag, and produce the writer's successor"
        "write-right"  "append an R tag, and produce the writer's successor"
        "open"         "open a reader at the start of a finished serialization"
        "new"          "make an empty writer"
        "finish"       "the writer owes nothing, so it becomes a finished value"
        "call"         "the callee starts with only what it was passed"
        "let-continue" "the right-hand side is done; bind what it produced and run the body"
        "scope"        "close a scope: drop its readers; no writer may be left in it"
        "call-return"  "the callee holds no writer; the caller's environments come back"))

;; ---------------------------------------------------------------------------
;; Drawing
;; ---------------------------------------------------------------------------

(define cell-size 30)
(define label-width 150)
(define lane-height 86)
(define stack-width 260)
(define frame-height 18)
(define frame-gap 3)
(define column-gap 30)

(define (hex digits)
  (make-object color%
               (string->number (substring digits 0 2) 16)
               (string->number (substring digits 2 4) 16)
               (string->number (substring digits 4 6) 16)))

(define ink (hex "1e1e1e"))
(define faint (hex "8a8a8a"))

(define (mono s [size 12] [color ink]) (colorize (text s 'modern size) color))
(define (sans s [size 12] [color ink]) (colorize (text s 'swiss size) color))
(define (bold s [size 13] [color ink]) (colorize (text s '(bold . swiss) size) color))

(define (lerp a b n) (+ a (* (- b a) n)))

;; The old picture is gone before the new one arrives, since two lines of text
;; drawn over each other at half strength are unreadable.
(define (crossfade a b n)
  (cond [(<= n 0) a]
        [(>= n 1) b]
        [else (lt-superimpose (cellophane a (max 0 (- 1 (* 2 n))))
                              (cellophane b (max 0 (- (* 2 n) 1))))]))

;; Draw `a` and `b` with `render` and fade between them, unless they are the
;; same data, in which case there is nothing to fade.
(define (fade-between a b n render)
  (if (equal? a b) (render b) (crossfade (render a) (render b) n)))

(define (clip-to p width [height (pict-height p)])
  (inset/clip p 0 0 (- width (pict-width p)) (- height (pict-height p))))

(define (dashed-box w h color)
  (dc (lambda (dc dx dy)
        (define old-pen (send dc get-pen))
        (define old-brush (send dc get-brush))
        (send dc set-pen (new pen% [color color] [width 1] [style 'short-dash]))
        (send dc set-brush "white" 'transparent)
        (send dc draw-rectangle dx dy w h)
        (send dc set-pen old-pen)
        (send dc set-brush old-brush))
      w h))

;; --- cells and cursors ------------------------------------------------------

(define (cell-color cell)
  (match cell ['L (hex "d4e4f7")] ['R (hex "f7dfc9")] [_ "white"]))

(define (cell-pict cell)
  (cc-superimpose
   (filled-rectangle cell-size cell-size #:color (cell-color cell) #:border-color (hex "5a5a5a"))
   (mono (cell->string cell) 13)))

(define reader-color (hex "1a5fb4"))
(define writer-color (hex "c01c28"))
(define yielded-color (hex "e66100"))
(define saved-color (hex "77767b"))

(define (occ-color o)
  (match (occ-place o)
    ['live (if (eq? (cap-kind (occ-cap o)) 'reader) reader-color writer-color)]
    ['yielded yielded-color]
    ['saved saved-color]))

;; A cursor: where it points, what it is called, its colour, and whether it
;; is a writer that still owes cells (and so has an empty slot to fill).
(struct cursor (pos name color slot?) #:transparent)

(define (occ-cursor o)
  (define cap (occ-cap o))
  (define kind (cap-kind cap))
  (cursor (if (eq? kind 'reader) (fourth cap) (length (cap-cells cap)))
          (or (occ-name o) "yielded")
          (occ-color o)
          (and (eq? kind 'writer) (pair? (cap-pending cap)))))

(define (cursor-pict c)
  (vc-append 0
             (colorize (arrowhead 11 (/ pi 2)) (cursor-color c))
             (mono (~a (cursor-name c)) 12 (cursor-color c))))

(define (cursor-x pos) (+ label-width (* pos cell-size) (/ cell-size 2)))

;; --- lanes -------------------------------------------------------------------

(define (view-alpha v)
  (case (view-status v) [(unborn) 0] [(gone) 0.4] [(present) 1]))

(define (view-heading v)
  (case (view-status v)
    [(unborn) '("" "")]
    [(gone) (list (symbol->string (view-kind v)) (view-note v))]
    [(present)
     (define places
       (remove-duplicates
        (for/list ([o (in-list (view-occs v))])
          (case (occ-place o)
            [(live) "live"] [(yielded) "in flight"] [(saved) "held by caller"]))))
     (list (symbol->string (view-kind v)) (string-join places ", "))]))

(define (view-protocol v)
  (if (eq? (view-status v) 'present)
      (string-append "owes " (protocol->string (cap-pending (occ-cap (first (view-occs v))))))
      ""))

(define (view-cursors v)
  (sort (map occ-cursor (view-occs v)) < #:key cursor-pos))

(define (heading-pict heading)
  (vl-append 2 (bold (first heading)) (sans (second heading) 11 faint)))

;; One lane, part way (n) from how it looks in `a` to how it looks in `b`.
(define (lane-pict a b n width)
  (define cells-a (if (eq? (view-status a) 'unborn) (view-cells b) (view-cells a)))
  (define cells-b (view-cells b))
  (define cells-y 4)
  (define cursor-y (+ cells-y cell-size 2))

  ;; A writer's new cell fades in where its old slot was; anything else
  ;; that changes cross-fades.
  (define (row cells alpha-from)
    (for/fold ([p (blank (* (length cells) cell-size) cell-size)])
              ([cell (in-list cells)] [i (in-naturals)])
      (pin-over p (* i cell-size) 0
                (cellophane (cell-pict cell) (if (>= i alpha-from) n 1)))))
  (define cells-row
    (cond [(prefix? cells-a cells-b) (row cells-b (length cells-a))]
          [else (crossfade (row cells-a +inf.0) (row cells-b +inf.0) n)]))

  ;; Cursors that correspond one to one slide; otherwise the old ones fade out
  ;; while the new ones fade in.
  (define cursors-a (if (eq? (view-status a) 'unborn) (view-cursors b) (view-cursors a)))
  (define cursors-b (view-cursors b))
  (define placed-cursors
    (if (= (length cursors-a) (length cursors-b))
        (for/list ([ca (in-list cursors-a)] [cb (in-list cursors-b)])
          (list (lerp (cursor-pos ca) (cursor-pos cb) n)
                (fade-between ca cb n cursor-pict)
                (lerp (if (cursor-slot? ca) 1 0) (if (cursor-slot? cb) 1 0) n)
                1))
        (append
         (for/list ([c (in-list cursors-a)])
           (list (cursor-pos c) (cursor-pict c) (if (cursor-slot? c) 1 0) (- 1 n)))
         (for/list ([c (in-list cursors-b)])
           (list (cursor-pos c) (cursor-pict c) (if (cursor-slot? c) 1 0) n)))))

  (define with-cells
    (pin-over (blank width lane-height) label-width cells-y cells-row))
  (define with-cursors
    (for/fold ([p with-cells]) ([placed (in-list placed-cursors)])
      (match-define (list pos arrow slot alpha) placed)
      (define x (cursor-x pos))
      (define slotted
        (if (> slot 0)
            (pin-over p (- x (/ cell-size 2)) cells-y
                      (cellophane (dashed-box cell-size cell-size faint) (* slot alpha)))
            p))
      (pin-over slotted (- x (/ (pict-width arrow) 2)) cursor-y (cellophane arrow alpha))))
  (define with-heading
    (pin-over with-cursors 0 cells-y
              (fade-between (view-heading a) (view-heading b) n heading-pict)))
  ;; Below the cursors, since a protocol can be much wider than its buffer.
  (define with-protocol
    (pin-over with-heading label-width (+ cursor-y 30)
              (fade-between (view-protocol a) (view-protocol b) n
                            (lambda (s) (clip-to (mono s 12 faint) (- width label-width))))))
  (cellophane with-protocol (lerp (view-alpha a) (view-alpha b) n)))

;; --- the stack ---------------------------------------------------------------

(define (frame-look frame)
  (match frame
    [`(frame-let (bind ,xs ,rs) ,_ ,_)
     (list (format "let ~a" (string-join (map ~a (append xs rs)) " "))
           (hex "e8e8e8"))]
    [`(frame-scope ,_ ,rs)
     (list (format "scope ~a" (string-join (map ~a rs) " ")) (hex "d4e4f7"))]
    [`(frame-call ,_ ,held) (list "call" (hex "e2d6f3"))]))

(define (frame-pict frame)
  (match-define (list label color) (frame-look frame))
  (inset
   (lc-superimpose
    (filled-rounded-rectangle stack-width frame-height 4 #:color color #:border-color (hex "9a9a9a"))
    (inset (mono label 11) 6 0 0 0))
   0 0 0 frame-gap))

(define (frames-pict frames)
  (if (null? frames)
      (blank stack-width 0)
      (apply vl-append (map frame-pict frames))))

;; The stack grows downwards from the top.  Whatever the two stacks share at
;; the bottom stays put; the frames above it fade, and the space they take
;; grows or shrinks, so a push nudges everything below it down.
(define (stack-pict stack-a stack-b n height)
  (define shared
    (let loop ([ra (reverse stack-a)] [rb (reverse stack-b)] [k 0])
      (if (and (pair? ra) (pair? rb) (equal? (car ra) (car rb)))
          (loop (cdr ra) (cdr rb) (add1 k))
          k)))
  (define top-a (frames-pict (take stack-a (- (length stack-a) shared))))
  (define top-b (frames-pict (take stack-b (- (length stack-b) shared))))
  (define top
    (clip-to (crossfade top-a top-b n)
             stack-width
             (lerp (pict-height top-a) (pict-height top-b) n)))
  (define column (vl-append top (frames-pict (take-right stack-b shared))))
  (define title
    (fade-between (length stack-a) (length stack-b) n
                  (lambda (k) (sans (format "stack  (~a frame~a)" k (if (= k 1) "" "s")) 11 faint))))
  (define body-height (- height (pict-height title) 6))
  (vl-append 6 title (clip-to column stack-width body-height)))

;; --- the environment ---------------------------------------------------------

(define env-lines 6)

(define (environment-pict env)
  (define lines
    (for/list ([binding (in-list env)])
      (format "~a = ~a" (first binding) (value->string (second binding)))))
  (define shown (take lines (min env-lines (length lines))))
  (apply vl-append 3
         (sans "environment" 11 faint)
         (append
          (if (null? shown) (list (mono "empty" 12 faint)) (map mono shown))
          (if (> (length lines) env-lines)
              (list (mono (format "… ~a more" (- (length lines) env-lines)) 12 faint))
              '()))))

;; --- a whole frame -----------------------------------------------------------

(define (state-parts state)
  (match-define `(machine ,_ (config ,control ,env ,_ ,stack)) state)
  (values control env stack))

(define (banner-pict a-film b)
  (define rule (scene-rule b))
  (vl-append 4
             (hb-append 12
                        (bold (or rule "initial state") 22)
                        (sans (format "step ~a of ~a" (scene-index b) (sub1 (film-length a-film))) 12 faint))
             (sans (hash-ref rule-blurbs rule "the program, about to run") 14 (hex "444444"))))

;; The picture part way (n) through the step from scene `a` to scene `b`.
;; Every frame of a film has the same size, so frames can be shown one after
;; another without anything jumping.
(define (compose a-film a b n)
  (define-values (control-a env-a stack-a) (state-parts (scene-state a)))
  (define-values (control-b env-b stack-b) (state-parts (scene-state b)))
  (define max-cells (film-max-cells a-film))
  (define left-width
    (max 540 (+ label-width (* (add1 max-cells) cell-size))))
  (define lanes-y 112)
  (define env-y (+ lanes-y (* (film-lane-count a-film) lane-height) 10))
  (define height (+ env-y 20 (* (add1 env-lines) 17)))
  (define width (+ left-width column-gap stack-width))
  (define control
    (vl-append 3 (sans "control" 11 faint)
               (fade-between (control->string control-a) (control->string control-b) n
                             (lambda (s) (clip-to (mono s 14) left-width)))))
  (define lanes
    (for/fold ([p (blank left-width 0)])
              ([va (in-list (scene-views a))] [vb (in-list (scene-views b))])
      (vl-append p (lane-pict va vb n left-width))))
  (define-syntax-rule (place base [x y p] ...)
    (let* ([acc base] [acc (pin-over acc x y p)] ...) acc))
  (place (filled-rectangle width height #:color "white" #:draw-border? #f)
         [0 0 (banner-pict a-film b)]
         [0 62 control]
         [0 lanes-y lanes]
         [0 env-y (fade-between env-a env-b n environment-pict)]
         [(+ left-width column-gap) 0 (stack-pict stack-a stack-b n height)]))

(define (film-scene a-film i) (list-ref (film-scenes a-film) i))

;; Scene `i` on its own.
(define (film-frame a-film i)
  (define s (film-scene a-film i))
  (compose a-film s s 0))

;; Part way (n, from 0 to 1) through the step into scene `i`.
(define (film-transition a-film i n)
  (compose a-film (film-scene a-film (sub1 i)) (film-scene a-film i) n))

;; One state, drawn on its own with no film around it.
(define (state->pict state)
  (define-values (lanes assignments) (assign-lanes (list state)))
  (define views (lane-views lanes assignments))
  (define max-cells
    (for/fold ([widest 1]) ([v (in-list (first views))]) (max widest (length (view-cells v)))))
  (define alone (film (list (scene 0 #f state (first views))) (length lanes) max-cells))
  (film-frame alone 0))

;; ---------------------------------------------------------------------------
;; Saving
;; ---------------------------------------------------------------------------

;; To a .png (at twice the size, for sharpness) or a .pdf, by extension.
(define (save-pict p path)
  (define name (if (path? path) (path->string path) path))
  (cond
    [(regexp-match? #rx"[.]pdf$" name)
     (define dc (new pdf-dc% [interactive #f] [use-paper-bbox #f]
                     [width (pict-width p)] [height (pict-height p)]
                     [output name]))
     (send dc start-doc "pict")
     (send dc start-page)
     (draw-pict p dc 0 0)
     (send dc end-page)
     (send dc end-doc)]
    [else (send (pict->bitmap (scale p 2)) save-file name 'png)])
  (void))

(module+ test
  (require rackunit "examples.rkt")

  (define add1-film (run->film recursive-signatures (add1-tree-program sample-tree)))

  ;; Three buffers: the writer that builds the input, the reader opened on
  ;; it, and the writer building the output.
  (check-equal? (film-lane-count add1-film) 3)
  (check-equal? (map view-kind (scene-views (last (film-scenes add1-film))))
                '(writer reader writer))

  ;; Each lane holds one buffer all the way through, despite the renaming:
  ;; the input lane and the reader's lane hold the same cells, and the output
  ;; lane ends up with every leaf incremented.
  (define input '(R L (I 1) R L (I 2) L (I 3)))
  (check-equal? (film-lane-cells add1-film)
                (list input input '(R L (I 2) R L (I 3) L (I 4))))

  ;; The film is as long as the run.
  (check-equal? (length (film-scenes add1-film))
                (add1 (length (let loop ([s (term (initial ,recursive-signatures
                                                             ,(add1-tree-program sample-tree)))])
                                (match (apply-reduction-relation machine-step s)
                                  ['() '()]
                                  [(list next) (cons next (loop next))])))))

  ;; Every frame, and a point part way through every step, draws, and all of
  ;; them are the same size.
  (define sizes
    (remove-duplicates
     (for*/list ([i (in-range (film-length add1-film))]
                 [p (in-list (if (zero? i)
                                 (list (film-frame add1-film i))
                                 (list (film-frame add1-film i)
                                       (film-transition add1-film i 1/2))))])
       (list (pict-width p) (pict-height p)))))
  (check-equal? (length sizes) 1)

  ;; A lone state draws too.
  (check-true (pict? (state->pict (term (initial () ,build-seven))))))
