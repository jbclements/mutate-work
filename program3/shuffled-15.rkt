#lang typed/racket
(require typed/rackunit)

;;Added closures and environments, wrote some leper functions, started updating some of the interp.parse c
(define-type ExprC (U numC binopC ifleq0C idC appC))
(struct numC ([n : Real]) #:transparent)
(struct binopC ([o : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct ifleq0C ([x : ExprC] [t : ExprC] [f : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([exp : ExprC] [a : (Listof ExprC)]) #:transparent)
(struct lamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]))

;;Contains the list of type primitives that can be returned. Closure is a function definition. It also
;;has a list of bindings (or, an environment)
(define-type Value (U Real Boolean Closure))
(struct Closure ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)

;; Define environments
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof Binding))
(define mt-env empty)

;; valid binary operators
(define binary-operators (hash '+ + '* * '- - '/ /))

;;get-env: Returns an environment for the function
(define (get-env [params : (Listof Symbol)] [args : (Listof ExprC)] [env : Env]) : Env
  (reverse (map (lambda ([param : Symbol] [arg : ExprC]) (Binding param (interp arg env))) params args)))

;; lookup: looks up the binding in the provided environment
(define (lookup [s : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'ZNQR "lookup: ~e was not found in the environment." s)]
    [else (cond
            [(symbol=? s (Binding-name (first env))) (Binding-val (first env))]
            [else (lookup s (rest env))])]))

;; interp: Accepts the AST and returns arithmetic values
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(idC n) (lookup n env)]
    [(numC n) n]
    ;;From the book
    [(appC f a) (local ([define tmp (interp f env)])
       (match tmp
         [(Closure params body parent) (interp (Closure-body tmp) (append (get-env (Closure-params tmp) a env) parent))]
         [_ (error 'ZNQR "interp: ~e was not a procedure." tmp)]))]))

;; parse: maps Sexp to ArithS using the match form.
(define (parse [exp : Sexp]) : ExprC
  (match exp
    [(? real? n) (numC n)]
    [(? symbol?) (cond
       [(hash-has-key? binary-operators exp) (error 'ZNQR "parse: an invalid expression was detected: ~e" exp)]
       [(eq? 'ifleq0 exp) (error 'ZNQR "parse: an invalid expression was detected: ~e" exp)]
       [(eq? 'func exp) (error 'ZNQR "parse: an invalid expression was detected: ~e" exp)]
       [else (idC exp)])]
    ;;[else (error 'ZNQR "parse: an invalid expression form was detected: ~e" exp)]
    ))

;;parse-fundef: Takes in a fundefC and parses it
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    [(list 'func (list (? symbol? name) args ...) body) (FundefC name (check-args args) (parse body))]
    [else (error 'ZNQR "parse-fundef: invalid function detected: ~e" s)]))

;; check-args: Validates the arguments
(define (check-args [args : (Listof Sexp)]) : (Listof Symbol)
  (cond
    [(empty? args) '()]
    [(symbol? (first args)) (cons (first args) (check-args (rest args)))]
    [else (error 'ZNQR "check-args: invalid arguments were detected : ~e" args)]))

;; parse-prog: Takes in the entire program and returns a list of fundefs
(define (parse-prog [exp : Sexp]) : (Listof FundefC)
  (cond
    [(empty? exp) '()]
    [else (match exp
            [(? list?) (cons (parse-fundef (first exp)) (parse-prog (rest exp)))])]))

; Transform value to string
(: serialize
   (Value -> String))
(define (serialize v)
  (cond
    [(real? v) (number->string v)]
    [(boolean? v) (if v "true" "false")]
    [(Closure? v) "#<procedure>"]))

;;top-interp: Accepts an S-expression and calls the parser, and then the interp function.
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) mt-env)))



;;TESTING

