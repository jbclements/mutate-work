#lang typed/racket

;;> eyeball: 3/6, Good start, see comments below

(require typed/rackunit)


;--------------------comments--------------------------
; I finished all the functions but haven't written out all of the test cases
; for testing. (missing test cases for top-interp(), interp(), and op-handler())
;I failed to sumbit it through drracket becasue I don't have full coverage on test cases ...
; wish I have more time but ... yeah
; I'll keep working on it
;-----------------------------------------------------


;------------------------------_ZNQR3_H_------------------------------------------
(define EPSILON 0.001)

; definine Value
(define-type Value (U numV boolV stringV closureV opV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct stringV ([s : String]) #:transparent)
(struct closureV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct opV ([s : Symbol]) #:transparent)

; define Expression
(define-type ExprC (U NumC StringC IdC AppC LamC IfC))
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct IfC ([iff : ExprC] [then : ExprC] [else : ExprC]) #:transparent)


; define environment and Binding
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof Binding))
(define mt-env '())
(define extend-env append)

; define top-env with primitive operations
(define top-env
        (list (Binding '+ (opV '+))
                (Binding '- (opV '-))
                (Binding '* (opV '*))
                (Binding '/ (opV '/))
                (Binding '<= (opV '<=))
                (Binding 'equal? (opV 'equal?))))


;------------------------------functions---------------------------------------------

; gievn a program and parse it into a string
(define (top-interp [s : Sexp]) : String
        (serialize (interp (parse s) top-env)))

; given an s-expression, return an expression
(define (parse [s : Sexp]) : ExprC
        (match s
                [(? real? s) (NumC s)]
                [(? string? s) (StringC s)]
                [(list 'if a b c) (IfC (parse a) (parse b) (parse c))]
                [(list 'var arg ... body)
                        (AppC (parse (desugar-body body))
                                (map parse (desugar-arg (cast arg (Listof Sexp)))))]
                [(? symbol? s)
                        (if (is_valid s)
                                (IdC s)
                                (error "ZNQR: invalid symbol"))]
                [(list args '-> body)
                        (match args
                                [(list (? symbol? rst) ...)
                                        (if (or (check-repeated (set) (cast rst (Listof Symbol)))
                                                        (equal? rst '()))
                                                (error "ZNQR: bad syntax")
                                                (LamC (cast rst (Listof Symbol)) (parse body)))])]
                [(list fst rst ...)
                        (AppC (parse fst) (map parse rst))]))



; given an expression and environment, return a value
(define (interp [e : ExprC] [env : Env]) : Value
        (match e
                [(NumC n) (numV n)]
                [(StringC s) (stringV s)]
                [(IfC one two three)
                        (match (interp one env)
                          ;;> if should only allow for bools
                                [(numV n) (if (positive? n)
                                        (interp two env)
                                        (interp three env))]
                                [(boolV b) (if b
                                        (interp two env)
                                        (interp three env))])]
                [(IdC x) (lookup x env)]
                [(LamC args body) (closureV args body env)]
                [(AppC fun args)
                        (match (interp fun env)
                                [(opV s) (op-handler s args env)]
                                [(closureV args2 body cloEnv)
                                        (define new-env
                                          ;;> why are you appending cloEnv twice?
                                                (extend-env cloEnv
                                                        (map (lambda (n v)
                                                                (Binding (cast n Symbol) (interp (cast v ExprC) env)))
                                                                 args2 args)
                                                        cloEnv))
                                                (interp body new-env)])]))




; given a primitive operations, list of arguments, and an environment
; return a value
(define (op-handler [s : Symbol] [args : (Listof ExprC)] [env : Env]) : Value
        (match s
                ['+
                        (match (interp (first args) env)
                                [(numV a)
                                        (match (interp (second args) env)
                                                [(numV b) (numV (+ a b))])])]
                ['-
                        (match (interp (first args) env)
                                [(numV a)
                                        (match (interp (second args) env)
                                                [(numV b) (numV (- a b))])])]
                ['*
                        (match (interp (first args) env)
                                [(numV a)
                                        (match (interp (second args) env)
                                                [(numV b) (numV (* a b))])])]
                ['/
                        (match (interp (first args) env)
                                [(numV a)
                                        (match (interp (second args) env)
                                                [(numV b)
                                                        (if (zero? b)
                                                                (error "ZNQR: divided by 0")
                                                                (numV (/ a b)))])])]
                ['<=
                        (match (interp (first args) env)
                                [(numV a)
                                        (match (interp (second args) env)
                                                [(numV b)
                                                        (boolV (<= a b))])])]
                ['equal?
                        (match (interp (first args) env)
                                [(numV a)
                                        (match (interp (second args) env)
                                                [(numV b)
                                                        (boolV (equal? a b))])])]))



; given a Value, return a string
(define (serialize [v : Value]) : String
        (match v
                [(numV n) (~v n)]
                [(boolV b) (if b "true" "false")]
                [(stringV s) (~v s)]
                [(closureV args body env) "#<procedure>"]
                [(opV s) "#<primop>"]))


;------------------------------helper functions---------------------------------------

; given a key symbol and a enviroment
; return the value binds to the key in the given environment
(define (lookup [for : Symbol] [env : Env]) : Value
        (cond
                [(empty? env) (error "ZNQR: lookup name not found")]
                [else
                        (cond
                                [(equal? for (Binding-name (first env)))
                                        (Binding-val (first env))]
                                [else (lookup for (rest env))])]))



; takes in a symbol and determine if it is one of the reserveds symbols for ZNQR
(define (is_valid [s : Symbol]) : Boolean
        (not (or (equal? s '=) (equal? s '->)
                         (equal? s 'if) (equal? s 'var))))




; takes in an empty set and list of symbols return true if there's repeated symbol in the set
(define (check-repeated [set_of_args : (Setof Any)] [l : (Listof Symbol)] ) : Boolean
        (cond
                [(empty? l) #f]
                [else
                        (if (set-member? set_of_args (first l))
                                #t
                                (check-repeated (set-add set_of_args (first l)) (rest l)))]))


; desugar the body of var
(define (desugar-body [s : Sexp]) : Sexp
        (match s
                [(list (? symbol? fun) body ...)
                        (list body '-> (append (list fun) body))]))


; desugar the arguments of var
(define (desugar-arg [s : (Listof Sexp)]) : (Listof Sexp)
        (cond
                [(empty? s) '()]
                [else
                        (match (first s)
                                [(list _ '= body)
                                        (cons body (desugar-arg (rest s)))])]))




;------------------------------------test cases------------------------------------------


(check-equal? (is_valid 'var) #f)
(check-equal? (is_valid 'if) #f)
(check-equal? (is_valid '=) #f)
(check-equal? (is_valid '->) #f)
(check-equal? (is_valid 'x) #t)


(check-equal? (lookup '+ top-env) (opV '+))
(check-equal? (lookup 'equal? top-env) (opV 'equal?))
(check-exn (regexp (regexp-quote "ZNQR: lookup name not found"))
        (lambda () (lookup 'f top-env)))



(check-equal? (serialize (numV 34)) "34")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (stringV "hello")) "\"hello\"")
(check-equal? (serialize (closureV '(a b c d) (NumC 5) top-env)) "#<procedure>")
(check-equal? (serialize (opV '+)) "#<primop>")



(check-equal? (check-repeated (set 's) (list 'k 'w 'e)) #f)
(check-equal? (check-repeated (set 'f) (list 'x 'x)) #t)


(check-equal? (desugar-arg '{{z = {+ 9 14}} {y = 98}}) '{{+ 9 14} 98})

(check-equal? (desugar-body '{+ z y}) '{{z y} -> {+ z y}})


(check-equal? (parse '5) (NumC 5))
(check-equal? (parse '"hello") (StringC "hello"))
(check-equal? (parse '{{a b c} -> 3}) (LamC (list 'a 'b 'c) (NumC 3)))
(check-exn (regexp (regexp-quote "ZNQR: bad syntax"))
        (lambda () (parse '{{x y x } -> 8})))
(check-equal? (parse '{+ 1 3}) (AppC (IdC '+) (list (NumC 1) (NumC 3))))
(check-exn (regexp (regexp-quote "ZNQR: invalid symbol"))
        (lambda () (parse '{if 3})))
(check-equal? (parse '{if 1 2 3}) (IfC (NumC 1) (NumC 2) (NumC 3)))
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}})
                                (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                                        (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                                                (NumC 98))))
(check-exn (regexp (regexp-quote "ZNQR: bad syntax"))
        (lambda () (parse '((() -> 9) 17))))



(check-equal? (interp (NumC 5) top-env) (numV 5))
(check-equal? (interp (StringC "hello") top-env) (stringV "hello"))
(check-equal? (interp (IdC '+) top-env) (opV '+))
(check-equal? (interp (IfC (NumC 1) (NumC 2) (NumC 3)) top-env) (numV 2))
(check-equal? (interp (IfC (NumC 0) (NumC 2) (NumC 3)) top-env) (numV 3))
(check-equal? (interp (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))) top-env)
        (closureV '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))) top-env))
(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (NumC 2) (NumC 2)))
        (NumC 1) (NumC 0)) top-env) (numV 1))
(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (NumC 1) (NumC 2)))
        (NumC 1) (NumC 0)) top-env) (numV 0))
(define app1 (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                                        (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                                                (NumC 98))))
(check-equal? (interp app1 top-env) (numV 121))


(check-equal? (op-handler '+ (list (NumC 5) (NumC 2)) top-env) (numV 7))
(check-equal? (op-handler '- (list (NumC 2) (NumC 1)) top-env) (numV 1))
(check-equal? (op-handler '* (list (NumC 2) (NumC 1)) top-env) (numV 2))
(check-equal? (op-handler '/ (list (NumC 6) (NumC 2)) top-env) (numV 3))
(check-exn (regexp (regexp-quote "ZNQR: divided by 0"))
        (lambda () (op-handler '/ (list (NumC 2) (NumC 0)) top-env)))
(check-equal? (op-handler '<= (list (NumC 2) (NumC 1)) top-env) (boolV #f))
(check-equal? (op-handler 'equal? (list (NumC 2) (NumC 2)) top-env) (boolV #t))


(check-equal? (top-interp '5) "5")
(check-equal? (top-interp '"hello") "\"hello\"")
(check-equal? (top-interp '{{a b c} -> 3}) "#<procedure>")
(check-equal? (top-interp '+) "#<primop>")













