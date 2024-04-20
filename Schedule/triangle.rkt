#lang racket

(require rackunit)

(define (type-of-triangle side1 side2 side3)
  (cond
    [(or (<= side1 0) (<= side2 0) (<= side3 0)) "Not a triangle"]
    [(or (<= (+ side1 side2) side3)
         (<= (+ side2 side3) side1)
         (<= (+ side1 side3) side2)) "Not a triangle"]
    [(and (= side1 side2) (= side2 side3)) "Equilateral"]
    [(or (= side1 side2) (= side2 side3) (= side1 side3)) "Isosceles"]
    [else "Scalene"]))

; Test cases
(check-equal? (type-of-triangle 3 3 7) "Not a triangle")
(check-equal? (type-of-triangle 0 3 3) "Not a triangle")
(check-equal? (type-of-triangle 2 0 5) "Not a triangle")
(check-equal? (type-of-triangle 5 3 10) "Not a triangle")
(check-equal? (type-of-triangle 3 3 6) "Not a triangle")

(check-equal? (type-of-triangle 3 4 5) "Scalene")
(check-equal? (type-of-triangle 5 7 9) "Scalene")
(check-equal? (type-of-triangle 5 12 13) "Scalene")

(check-equal? (type-of-triangle 3 3 5) "Isosceles")
(check-equal? (type-of-triangle 5 5 9) "Isosceles")
(check-equal? (type-of-triangle 12 13 13) "Isosceles")
(check-equal? (type-of-triangle 9 8 8) "Isosceles")

(check-equal? (type-of-triangle 3 3 3) "Equilateral")
(check-equal? (type-of-triangle 1 1 1) "Equilateral")
(check-equal? (type-of-triangle 6 6 6) "Equilateral")