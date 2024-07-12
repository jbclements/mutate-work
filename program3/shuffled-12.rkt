#lang typed/racket

;;> eyeball: 2/6, Thank you for the progress comment

(require typed/rackunit)

; Binding definition
(struct Binding ([name : Symbol] [val : Value]))
; Environment definition
(define-type-alias Environment (Listof Binding))

; Value definition
(define-type Value (U Number Boolean Closure Primop '()))
(struct Closure ([args : (Listof Symbol)] [body : ExprC] [env : Environment]) #:transparent)
(struct Primop ([op : (Number Number -> Number)]) #:transparent)

; ExprC definition
(define-type ExprC (U ValueC IDC AppC))
(struct ValueC ([v : Real]) #:transparent)
(struct IDC ([id : Symbol]) #:transparent)
(struct AppC ([fname : Symbol] [args : (Listof ExprC)]) #:transparent)
; FundefC definition
(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)

; Top-level environment
(define top-env (list (Binding 'true #t) (Binding 'false #f)
                      (Binding '+ (Primop +)) (Binding '- (Primop -)) (Binding '* (Primop *)) (Binding '/ (Primop /))
                      (Binding 'hello (Closure '(a) (IDC 'a) '())) (Binding 'a 3)))

; lookup function
; consumes an identifier and an environment
; returns the value of that identifier
(define (lookup [for : Symbol] [env : Environment]) : Value
  (cond
    [(empty? env) (error "ZNQR: Attepmted to lookup an identifier not yet created.")]
    [else (cond
            [(equal? (Binding-name (first env)) for) (Binding-val (first env))]
            [else (lookup for (rest env))])]))
; Tests
(check-equal? (lookup 'ww (list (Binding 'ww #f) (Binding 'p 15))) #f)
(check-exn (regexp (regexp-quote "ZNQR: Attepmted to lookup an identifier not yet created."))
                   (lambda () (lookup 'p '())))

; serialize function
; consumes a Value
; returns a string that represents the corresponding Value
(define (serialize [v : Value]) : String
  (cond
    [(number? v) (~v v)]
    [(boolean? v) (if v "true" "false")]
    [(Closure? v) "#<procedure>"]
    [(Primop? v) "#<primop>"]
    [else (error "ZNQR: Invalid value.")]))
; Tests
(check-equal? (serialize 18) "18")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (lookup 'hello top-env)) "#<procedure>")
(check-equal? (serialize (lookup '+ top-env)) "#<primop>")
(check-exn (regexp (regexp-quote "ZNQR: Invalid value."))
           (lambda () (serialize '())))

; Concrete code examples
(define concrete1 '{ifleq0 2 -1 1}) ; Ans: 1
(define concrete2 '{+ 3 {* 8 2}}) ; Ans: 19
(define concrete3 '{* {- 3 10} 5}) ; Ans: -35
(define wroncrete '{7 * 29})

; parse function
; consumes an s-expression
; returns an ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? s) (ValueC s)]
    [(? symbol? s) (IDC s)]
    [(list (and (? symbol? funcname) funcname) param ...)
      (AppC funcname (map parse param))]
    [else (error "ZNQR: Invalid expression.")]))
; Tests
(check-equal? (parse concrete2) (AppC '+ (list (ValueC 3) (AppC '* (list (ValueC 8) (ValueC 2))))))
(check-equal? (parse concrete3) (AppC '* (list (AppC '- (list (ValueC 3) (ValueC 10))) (ValueC 5))))
(check-equal? (parse '{fn 3 8}) (AppC 'fn (list (ValueC 3) (ValueC 8))))
(check-exn (regexp (regexp-quote "ZNQR: Invalid expression."))
           (lambda () (parse wroncrete)))

; Function definitions for testing
(define func1 '{func {happy x y} {+ x y}})
(define funcwrong '{func not {a good definition} insides})
(define funcworse '{func {0 params} (* some numbers)})

; parse-function function
; consumes an s-expression
; returns a FundefC
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    [(list 'func (list name sym ...) expression)
      (cond
        [(and (andmap symbol? sym) (symbol? name)) (FundefC name sym (parse expression))]
        [else (error "ZNQR: Invalid function definition.")])]
    [else (error "ZNQR: Invalid function definition.")]))
; Tests
(check-equal? (parse-fundef func1) (FundefC 'happy (list 'x 'y) (AppC '+ (list (IDC 'x) (IDC 'y)))))
(check-exn (regexp (regexp-quote "ZNQR: Invalid function definition."))
           (lambda () (parse-fundef funcwrong)))
(check-exn (regexp (regexp-quote "ZNQR: Invalid function definition."))
           (lambda () (parse-fundef funcworse)))

; Function list definitions for tests
(define testfuncs1 (list (FundefC 'f (list 'x 'y) (AppC '+ (list (IDC 'x) (IDC 'y))))
                                     (FundefC 'main '() (AppC 'f (list (ValueC 1) (ValueC 2))))))

; interp function
; consumes an ExprC to evaluate (exp) using a given list of FundefC (funs)
; returns a real, which is the result of the ExprC
(define (interp [exp : ExprC] [env : Environment]) : Value
  (match exp
    [(ValueC v) v]
    [(IDC id) (lookup id env)]
    [(AppC fname params)
      (define fdef (lookup fname env))
      (cond
        [(Closure? fdef) (interp (Closure-body fdef) (map (lambda ([arg : Symbol] [par : ExprC])
                                                          (Binding arg (interp par env)))
                                                          (Closure-args fdef) params))]
        [(Primop? fdef) (cond
                          [(andmap ValueC? params)
                           ((Primop-op fdef) (ValueC-v (first params)) (ValueC-v (first (rest params))))]
                          [else (error "ZNQR: Attempted to evaluate an arithmetic operator on non-numbers.")])]
        [else (error "ZNQR: Attempted to reference an environment symbol which is not a closure.")])]))
; Tests
(check-equal? (interp (ValueC 7) top-env) 7)
(check-equal? (interp (IDC 'true) top-env) #t)
(check-equal? (interp (AppC 'hello (list (IDC 'a))) top-env) 3)
(check-equal? (interp (AppC '* (list (ValueC 8) (ValueC -4))) top-env) -32)
(check-equal? (interp (AppC '- (list (ValueC 8) (ValueC 3))) top-env) 5)
(check-exn (regexp (regexp-quote "ZNQR: Attempted to evaluate an arithmetic operator on non-numbers."))
           (lambda () (interp (AppC '- (list (ValueC 8) (IDC 'true))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Attempted to reference an environment symbol which is not a closure."))
           (lambda () (interp (AppC 'a '()) top-env)))

; top-interp function
; consumes an s-expression
; returns a real, which is the result of the input program
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))
; Tests
(check-equal? (top-interp '{hello 5}) "5")
