#lang typed/racket
(require typed/rackunit)

;;> partial-credit: 2/26, doesn't compile. :(

; Assignment 3, CSC 430, Spring 2019
; Goal: Implement an interpreter for higher-order language
; including booleans,strings, and local variable bindings

; Assignment not complete!

; immutable hash table or list
; change ifleq0 to if
; remove subst

; numC: real number
; binop: binary operation defined in a list
; idC: variable used in a function (x or y)
; appC: application of a function (function name, list of arguments)
; ifC - if-then-else
; lamC: lambda with list of arguments/body

;Data Structures
(define-type ExprC (U numC ifC binop idC appC lamC))
  (struct numC ([n : Real])#:transparent)
  (struct ifC ([if : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
  (struct binopC ([o : Symbol] [l : ExprC] [r : ExprC])#:transparent)
  (struct idC ([s : Symbol])#:transparent)
  (struct appC ([fun : Symbol] [arg : (Listof ExprC)])#:transparent)
  (struct lamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

; Return Type (#, boolean or closure)
(define-type Value (U numV boolV closeV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct closeV ([params : (Listof Symbol)] [body : ExprC] [close-env : Env]) #:transparent)

;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

; Top-Level Environment
#|
(+ a b) -> real
(- a b) -> real
(* a b) -> real
(/ a b) -> real
(<= a b) -> boolean
(equal? a b) -> boolean
true: boolean
false: boolean
|#

(define-type Env (Immutable-HashTable Symbol Value))
;extend environment -> returns new environment 
;(define extend-env [env : Env] [params : (Listof Symbol)] [args : (Listof ExprC)]) : Env


;hash table (binary operators)
(define top-level (make-immutable-hash
                   (list (cons '+ +)
                         (cons '- -)
                         (cons '* *)
                         (cons '/ /)
                         (cons '<= <=)
                         (cons 'equal? equal?)
                         (cons 'true (boolV #true))
                         (cons 'false (boolV #false)))))

;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

; Top-Level Functions
;calls interpreters and parsers
;returns value evaluated as string
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; Serialize: should accept ZNQR3 value, return a string
; example 34 -> "34"
; #<procedure>" #<primop>
(define (serialize [val : Value]) : String
  (match val
    [(numV n) (~v n)]
    [(boolV boo) (match boo
                    [#t "true"]
                    [#f "false"])]
    [(closeV a b c) "#<procedure>"]))
;primitive operators #<primop>


;::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
;Parsing Functions
;parse s expressions ->  ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? s) (numC s)]
    [(? equal? s 'true) (boo #t)]
    [(? equal? s 'false) (boo #f)]))
    ;[(? symbol? s)


;::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::                  
; Interp Functions
    
;takes ExprC function/environment and returns its value as value type
(define (interp [exp : ExprC] [env : Env]) : Value)
  (match exp
    [(numC n) (NumV n)]
    [(idC x) (look env x)] ;define look
    [(binopC x y z) (interp-binop x (interp x env) (interp z env))]
    [(ifC a b c) (cond [(check-if (interp a env)) (interp b env)]
                       [else (interp c env)])
                       (error 'boo "ZQNR: Error")]
    [(lamC a b) (closeV a b env)]
    [(appC f a) (match (interp f env))])) ;closed environment

;define look (to find symbol)
;(define (look [for : Symbol] [env : Env]) : Value

    
;::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
;Test Cases
  
;Seralize
;Top-Interp
;(check-exn