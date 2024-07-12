#lang typed/racket
(require typed/rackunit)


; The base cost to run a show
(define show-cost : Real 20)
; Extra cost per attendee
(define attendee-cost : Real 0.5)
; The price the attendees pay to see the show
(define ticket-price : Real 5)

; Calculates the profit from the number of attendees to a show, consumes number of attendees
(define (total-profit [num_attendees : Integer]) : Real
  (- (* num_attendees ticket-price) (* num_attendees attendee-cost) show-cost))

(check-= (total-profit 20) 70.0 0.1)
(check-= (total-profit 0) -20.0 0.1)

; Determines the surface area of the cylinder from it's base disk and height
(define (area-cylinder [radius : Real] [height : Real]) : Real
  (+
   (* 2 (* pi radius radius))
   (* 2 pi radius height))
  )

(check-= (area-cylinder 2 3) (* 20 pi) 0.1)
(check-= (area-cylinder 3 4) (* 42 pi) 0.1)
(check-= (area-cylinder 0 0) 0 0.1)

; represents a writing implement
(define-type Writer (U Pen Pencil))
; ink volume in ml, how-full a number in the range 0.0 to 1.0
(struct Pen ([ink-volume : Real] [how-full : Real]) #:transparent)
; length in cm
(struct Pencil ([length : Real]) #:transparent)

; Defines how many meters a pen can write for a ml of ink
(define m-per-ml : Real 150)
; Defines how many meters a pencil can write for a cm of length
(define m-per-cm : Real 56)

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (how-far-to-write [implement : Writer]) : Real
;  (cond
;    [(Pen? implement) (* m-per-ml (Pen-ink-volume implement) (Pen-how-full implement))]
;    [(Pencil? implement) (* m-per-cm (Pencil-length implement))]
;    )
;  )

; Determines how far a writing implement can write
(define (how-far-to-write [implement : Writer]) : Real
  (match implement
    [(Pen vol fillperc) (* m-per-ml vol fillperc)]
    [(Pencil len) (* m-per-cm len)]
    ))

(check-= (how-far-to-write (Pen 4 0.3)) (* 4 0.3 m-per-ml) 0.1)
(check-= (how-far-to-write (Pencil 4)) (* 4 m-per-cm) 0.1)

; represents either a first or second degree polynomial
(define-type Polynomial (U Linear Quadratic))
(struct Linear ([A : Real] [B : Real]) #:transparent)
(struct Quadratic ([A : Real] [B : Real] [C : Real]) #:transparent)

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (interp [poly : Polynomial] [x : Real]) : Real
;  (cond
;    [(Linear? poly)
;     (+
;      (* (Linear-A poly) x)
;      (Linear-B poly))]
;    [(Quadratic? poly)
;     (+
;      (* (Quadratic-A poly) (* x x))
;      (* (Quadratic-B poly) x)
;      (Quadratic-C poly))]))

; Evaluates a polynomial at a given x value
(define (interp [poly : Polynomial] [x : Real]) : Real
  (match poly
    [(Linear a b) (+ (* a x) b)]
    [(Quadratic a b c) (+ (* a (* x x)) (* b x) c)]
    ))

(check-= (interp (Linear 3 2) 1) 5 0.1)
(check-= (interp (Quadratic 3 2 1) 1) 6 0.1)
(check-= (interp (Linear 3 2) 2) 8 0.1)
(check-= (interp (Quadratic 3 2 1) 2) 17 0.1)
(check-= (interp (Linear 0 0) 1) 0 0.1)
(check-= (interp (Quadratic 1 0 0) 1) 1 0.1)

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (derivative [poly : Polynomial]) : Polynomial
;  (cond
;    [(Linear? poly)
;     (Linear 0 (Linear-A poly))]
;    [(Quadratic? poly)
;     (Linear (* 2 (Quadratic-A poly)) (Quadratic-B poly))]))

; Computes the derivative of the given polynomial
(define (derivative [poly : Polynomial]) : Polynomial
  (match poly
    [(Linear a b) (Linear 0 a)]
    [(Quadratic a b c) (Linear (* 2 a) b)]))

(check-equal? (derivative (Linear 2 4)) (Linear 0 2))
(check-equal? (derivative (Linear 0 4)) (Linear 0 0))
(check-equal? (derivative (Quadratic 2 4 1)) (Linear 4 4))
(check-equal? (derivative (Quadratic 1 0 0)) (Linear 2 0))

; A binary tree with symbols at the leafs
(define-type BTree (U Node Leaf))
(struct Node ([left : BTree] [right : BTree]) #:transparent)
(struct Leaf ([val : Symbol]) #:transparent)

(define tree1 (Leaf 'a))
(define tree2 (Node (Leaf 'a) (Leaf 'b)))
(define tree3 (Node (Node (Leaf 'a) (Leaf 'b)) (Node (Leaf 'c) (Leaf 'd))))

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (zz-tree [tree : BTree]) : BTree
;  (cond
;    [(Node? tree)
;     (Node (zz-tree (Node-left tree)) (zz-tree (Node-right tree)))]
;    [(Leaf? tree)
;     (Leaf 'zz)]))

; Replaces all leaf values with 'zz
(define (zz-tree [tree : BTree]) : BTree
  (match tree
    [(Node l r) (Node (zz-tree l) (zz-tree r))]
    [(Leaf val) (Leaf 'zz)]
    ))

(check-equal? (zz-tree tree1) (Leaf 'zz))
(check-equal? (zz-tree tree2) (Node (Leaf 'zz) (Leaf 'zz)))
(check-equal? (zz-tree tree3) (Node (Node (Leaf 'zz) (Leaf 'zz)) (Node (Leaf 'zz) (Leaf 'zz))))


; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (mirror [tree : BTree]) : BTree
;  (cond
;    [(Node? tree)
;     (Node (mirror (Node-right tree)) (mirror (Node-left tree)))]
;    [(Leaf? tree)
;     (Leaf (Leaf-val tree))]))

; Takes a binary tree and mirrors it, left child swaps with right
(define (mirror [tree : BTree]) : BTree
  (match tree
    [(Node l r) (Node (mirror r) (mirror l))]
    [(Leaf val) (Leaf val)]
    ))

(check-equal? (mirror tree1) (Leaf 'a))
(check-equal? (mirror tree2) (Node (Leaf 'b) (Leaf 'a)))
(check-equal? (mirror tree3) (Node (Node (Leaf 'd) (Leaf 'c)) (Node (Leaf 'b) (Leaf 'a))))

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (min-depth [tree : BTree]) : Integer
;  (cond
;    [(Node? tree) (if
;                   (< (min-depth (Node-left tree)) (min-depth (Node-right tree)))
;                   (+ (min-depth (Node-left tree)) 1)
;                   (+ (min-depth (Node-right tree)) 1))]
;    [(Leaf? tree) 0]))

; Calculates the shortest path to a leaf in a given tree
(define (min-depth [tree : BTree]) : Integer
  (match tree
    [(Node l r) (if
                 (< (min-depth l) (min-depth r))
                 (+ (min-depth l) 1)
                 (+ (min-depth r) 1))]
    [(Leaf val) 0]
    ))

(check-= (min-depth tree1) 0 0.1)
(check-= (min-depth tree2) 1 0.1)
(check-= (min-depth tree3) 2 0.1)
(check-= (min-depth (Node
                     (Node
                      (Node
                       (Node (Leaf 'a) (Leaf 'b))
                       (Leaf 'c))
                      (Leaf 'd))
                     (Leaf 'e))) 1 0.1)
(check-= (min-depth (Node (Leaf 'a) (Node (Leaf 'b) (Leaf 'c)))) 1 0.1)

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (occurrences [tree : BTree] [symbol : Symbol]) : Integer
;  (cond
;    [(Node? tree) (+ (occurrences (Node-left tree) symbol) (occurrences (Node-right tree) symbol))]
;    [(Leaf? tree) (if (eq? symbol (Leaf-val tree)) 1 0)]
;    ))

; Returns the number of occurances of a given symbol in a BTree
(define (occurrences [tree : BTree] [symbol : Symbol]) : Integer
  (match tree
    [(Node l r) (+ (occurrences l symbol) (occurrences r symbol))]
    [(Leaf val) (if (eq? symbol val) 1 0)]
    ))

(check-= (occurrences tree1 'a) 1 0.1)
(check-= (occurrences tree1 'foo) 0 0.1)
(check-= (occurrences (Node
                         (Node
                          (Node (Leaf 'a) (Leaf 'a))
                          (Node (Leaf 'a) (Leaf 'a)))
                         (Node (Leaf 'a) (Leaf 'a)))
                     'a) 6 0.1)

; Vestigial code from when I was doing everything with cond statements.
; I'm leaving it to use as a reference between the two
;(define (subst [tree : BTree] [symbol : Symbol] [repl : BTree]) : BTree
;  (cond
;    [(Node? tree) (Node (subst (Node-left tree) symbol repl) (subst (Node-right tree) symbol repl))]
;    [(Leaf? tree) (if (eq? symbol (Leaf-val tree)) repl tree)]))

; Substitues every leaf value with the given symbol in a BTree
(define (subst [tree : BTree] [symbol : Symbol] [repl : BTree]) : BTree
  (match tree
    [(Node l r) (Node (subst l symbol repl) (subst r symbol repl))]
    [(Leaf val) (if (eq? symbol val) repl tree)]))

(check-equal? (subst tree1 'a (Node (Leaf 'z) (Leaf 'z))) (Node (Leaf 'z) (Leaf 'z))) 
(check-equal? (subst tree2 'b (Node (Leaf 'z) (Leaf 'z))) (Node (Leaf 'a) (Node (Leaf 'z) (Leaf 'z))))
(check-equal? (subst tree3 'c (Node (Leaf 'z) (Leaf 'z))) (Node
                                                           (Node (Leaf 'a) (Leaf 'b))
                                                           (Node
                                                            (Node (Leaf 'z) (Leaf 'z)) (Leaf 'd))))

; is 2.11 optional? All path lengths...
