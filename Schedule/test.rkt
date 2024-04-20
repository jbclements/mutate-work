#lang racket

(require rackunit)

(define (is-positive num)
  (if (> num 0) #t
      #f))

(check-equal? (is-positive 5) #t)
(check-equal? (is-positive -1) #f)
  