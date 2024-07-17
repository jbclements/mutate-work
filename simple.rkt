#lang typed/racket
(define (foo)
    ; (cond 
    ;     [(and 1 2) 1]
    ;     [#t (+ 1 2 3)]
    ;     [(or 1 4 5) (and #t #t)]
    ;     [else 2])
    ; (if #t 1 2)
    (or 1 2 3)
)