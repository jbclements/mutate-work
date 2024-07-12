#lang typed/racket

;;> eyeball: 2/6, Thanks for the progress comment, see comment below

(require typed/rackunit)
;(require rackunit)

;2.2 Progress Toward Goal comment:
;I struggled with this project. I could not get parse and other parts of interp
;working. I was able to get parts of 3.2, serialize, and 3.3 Top-level env's working

;;> remember to start with test cases to help you understand what you need to do

;ExprC data type
(define-type ExprC (U NumC ifC appC))
   (struct NumC ([n : Real]) #:transparent)
   (struct StringC ([s : Symbol]) #:transparent)
   (struct ifC ([test : ExprC][then : ExprC][else : ExprC]) #:transparent)
   (struct appC ([args : (Listof ExprC)])#:transparent)

(define-type Value (U Real Boolean String ExprC))
(define-type Environment Value)

;takes ZNQR3 value and returns a string
(define (serialize [val : Value]) : String
   (match val
    [(? real? v) (~v v)]
    [(? boolean?)
     (match val
       [#t "true"]
       [_ "false"])]
    [(? string? v ) ~v v]
    [_ "#<procedure>"])
  )

;3.3 Top-level Env
;compute addition
(define (add [a : Real] [b : Real]) : Real
  (cond
    [(and (real? a) (real? b)) (+ a b)]
    ;[else (error "ZNQR: either a or b is not a number")]
    )
  )

;compute substition
(define (substitution [a : Real] [b : Real]) : Real
  (cond
    [(and (real? a) (real? b)) (- a b)]
    ;[else "ZNQR: either a or b is not a number"]
    )
  )

;compute multiplication
(define (mult [a : Real] [b : Real]) : Real
  (cond
    [(and (real? a) (real? b)) (* a b)]
    ;[else "ZNQR: either a or b is not a number"]
    )
  )

;parses an expression
(define (parse [s : Sexp]) : ExprC
  (NumC 1)
  )

;Interprets an expression
(define (interp [e : ExprC] [env : Environment]) : Value
  (NumC 1)
  )

;top-env(
(define (top-env) : Environment
  (NumC 1)
  )

;combines parsing and evaluation
(define (top-interp [s : Sexp]) : String
  ;(serialize (interp (parse s) top-env)))
  "v"
  )



;all test cases

;Test Cases Serialize
(check-equal? (serialize 430) "430")
(check-equal? (serialize true) "true")
(check-equal? (serialize false) "false")
(check-equal? (serialize "test") "test")
(check-equal? (serialize (NumC 1)) "#<procedure>")

;test case add
(check-equal? (add 4 5) 9)

;test case substitution
(check-equal? (substitution 5 1) 4)

;test case multiplication
(check-equal? (mult 5 1) 5)

;Test Case parse
(check-equal? (parse 1) (NumC 1))

;Test Case interp
(check-equal? (interp (NumC 1) (NumC 1)) (NumC 1))

;Test Case top-env
(check-equal? (top-env) (NumC 1))

;Test Cases top-interp
(check-equal? (top-interp 1) "v")
