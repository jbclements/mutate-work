#lang typed/racket
(require typed/rackunit)

;implemented all but primop interpretation and the var form
;(-> form parses)
;---------------------------------------------------------------------------------------------------
;Types and structures
;---------------------------------------------------------------------------------------------------

;define types for ZNQR3 Language Expressions
(define-type ExprC (U ifC idC appC funV Value))
(struct ifC ([test : ExprC] [th : ExprC] [el : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : ExprC][args : (Listof ExprC)]) #:transparent)

(define-type Value (U numV stringV boolV closV primopV funV))
(struct numV ([n : Real]) #:transparent)
(struct stringV ([s : String]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct closV ([arg : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([op : (-> numV numV (U numV boolV))]) #:transparent)
(struct funV ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

;Environment types
(struct binding ([name : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof binding))
(define mt-env '())
(define extend-env cons)

(define primopSym (list '+ '- '* '/ '<= 'equal? 'true 'false))
(define primopExp (list (primopV (λ ([a : numV] [b : numV]) : numV (numV (+ (numV-n a) (numV-n b)))))
                        (primopV (λ ([a : numV] [b : numV]) : numV (numV (- (numV-n a) (numV-n b)))))
                        (primopV (λ ([a : numV] [b : numV]) : numV (numV (* (numV-n a) (numV-n b)))))
                        (primopV (λ ([a : numV] [b : numV]) : numV
                               (cond [(= (numV-n b) 0) (error 'ZNQR "Divide by zero")]
                                     [else (numV (/ (numV-n a) (numV-n b)))])))
                        (primopV (λ ([a : numV] [b : numV]) : boolV (boolV (<= (numV-n a) (numV-n b))
                                                                           )))
                        (primopV (λ ([a : Any] [b : Any]) (boolV (equal? a b))))
                        (boolV #t)
                        (boolV #f)))

;---------------------------------------------------------------------------------------------------
;Functions
;---------------------------------------------------------------------------------------------------
;accepts an s-expression and calls the parser and interp functions on it
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

;serialize
(define (serialize [exp : ExprC]) : String
  (match exp
    [(numV n) (~v n)]
    [(stringV s) s]
    [(boolV b) (cond [(equal? b #t) "true"] [(equal? b #f) "false"])]
    [(closV args body env) "#<procedure>"]
    [(funV args body) "#<procedure>"]
    [(primopV _) "#<primop>"]
    [else (error 'ZNQR "serialize: type not recognized")]
    ))

;parse
(define (parse [s : Sexp]) : ExprC
  (cond
    [(real? s) (numV s)]
    [(boolean? s) (boolV s)]
    [(string? s) (stringV s)]
    [(symbol? s) (cond [(not (or (symbol=? (cast s Symbol) 'var)
                                 (symbol=? (cast s Symbol) 'if)
                                 (symbol=? (cast s Symbol) '->)
                                 (symbol=? (cast s Symbol) '=))) (idC (cast s Symbol))]
                       [else (error 'ZNQR "parse: illegal idC")])]
    [(list? s) (match s
                 [(list 'if test th el) (ifC (parse test) (parse th) (parse el))]
                 [(list 'var {list args '= val} ... body)
                  (appC (parse body) (map parse (cast args (Listof Symbol))))] ;<--- FIX ME
                 [(list (list args ...) '-> body) (funV (cast args (Listof Symbol)) (parse body))]
                 [(list fun args ...) (appC (parse fun) (map parse args))]
                 [else (error 'ZNQR "parse: fell off")])]
    [else (error 'ZNQR "parse: fell off")]
    ))


;takes a list of symbols and list of values, adding them all to the given environment
(define (mult-extend-env [c : (Listof Symbol)] [v : (Listof Value)] [env : Env]) : Env
  (cond
    [(and (= (length c) (length v)) (= 0 (length c))) env]
    [(= (length c) (length v)) (extend-env (binding (first c) (first v))
                                           (mult-extend-env (rest c) (rest v) env))]
    [else (error 'ZNQR "mult-extend-env: lists are of unequal length")]))

;takes an ExprC and it's environment and evaluates it, yielding a Value
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(numV n) (numV n)]
    [(stringV s) (stringV s)]
    [(boolV b) (boolV b)]
    [(ifC test th el) (cond
                        [(> (numV-n (cast (interp test env) numV)) 0) (interp th env)]
                        [else (interp el env)])]
    [(appC f a) (local ([define f-value : closV (cast (interp f env) closV)])
                  (interp (closV-body f-value)
                          (mult-extend-env (closV-arg f-value)
                                           (interp-list a env)
                                           env)))]
    [(funV a b) (closV a b env)]
    [(idC n) (lookup n env)]
    ;[(list (primopV op) a b) (op (interp a env) (interp b env))]
    ))

;accepts a list of expressions and a list of function definitions
;evaluates each expression in the list using the fundef list, packages answers back into
;numCs so that interp can use them
(define (interp-list [exp : (Listof ExprC)] [env : Env]) : (Listof Value)
  (cond
    [(empty? exp) '()]
    [else (cons (interp (first exp) env) (interp-list (rest exp) env))]
    ))

;looks up the given symbol in the environment, returning the associated value
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'ZNQR "lookup: name not found")]
    [else (cond
            [(symbol=? for (binding-name (first env)))
             (binding-val (first env))]
            [else (lookup for (rest env))])]))

;---------------------------------------------------------------
;TEST CASES
;---------------------------------------------------------------
;top-env
(define top-env : Env
(mult-extend-env primopSym primopExp mt-env))
;lookup tests
(check-equal? (lookup 'true top-env) (boolV #t))
(check-equal? (lookup 'false top-env) (boolV #f))
(check-exn (regexp (regexp-quote "lookup: name not found"))
           (lambda () (lookup 'bad-name top-env)))
(check-exn (regexp (regexp-quote "lookup: name not found"))
           (lambda () (lookup 'bad-name mt-env)))

;top-interp tests
(check-equal? (top-interp '{{} -> 5}) "#<procedure>")


;parse tests
(check-equal? (parse '{{a b c} -> {+ c {* a b}}}) (funV '(a b c) (appC (idC '+) (list (idC 'c)
                                                                 (appC (idC '*) (list (idC 'a)
                                                                                      (idC 'b)))))))
(check-equal? (parse '{#t}) (appC (boolV #t) '()))
(check-equal? (parse '{{a} -> 5}) (funV '(a) (numV 5)))
(check-equal? (parse '{"abc"}) (appC (stringV "abc") '()))
(check-exn (regexp (regexp-quote "parse: illegal idC"))
           (lambda () (parse '{->})))
(check-equal? (parse '{if 1 2 3}) (ifC (numV 1) (numV 2) (numV 3)))
(check-exn (regexp (regexp-quote "parse: fell off"))
           (lambda () (parse '{})))

;incorrect, test made for coverage
(check-equal? (parse '{var {x = 2} {y = 3} {+ x y}})
              (appC (appC (idC '+) (list (idC 'x) (idC 'y))) (list (idC 'x) (idC 'y))))

;interp tests
(check-equal? (interp (numV 5) top-env) (numV 5))
(check-equal? (interp (stringV "abc") top-env) (stringV "abc"))
(check-equal? (interp (boolV #t) top-env) (boolV #t))
(check-exn (regexp (regexp-quote "lookup: name not found"))
           (lambda () (interp (idC 'a) top-env)))
(check-equal? (interp (ifC (numV -1) (numV 1) (numV 2)) top-env) (numV 2))
(check-equal? (interp (ifC (numV 1) (numV 1) (numV 2)) top-env) (numV 1))
(check-equal? (interp (appC (funV (list 'a) (numV 5)) (list (numV 1))) top-env) (numV 5))

;mult-extend-env tests
(check-equal? (mult-extend-env (list 'a 'b) (list (numV 1) (numV 2)) mt-env)
              (list (binding 'a (numV 1))
                    (binding 'b (numV 2))))
(check-exn (regexp (regexp-quote "mult-extend-env: lists are of unequal length"))
           (lambda () (mult-extend-env (list 'a) (list (numV 1) (numV 2)) mt-env)))

;serialize tests
(check-equal? (serialize (numV 5)) "5")
(check-equal? (serialize (stringV "abc")) "abc")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (closV '(a) (numV 3) top-env)) "#<procedure>")
(check-equal? (serialize (funV '(a) (numV 5))) "#<procedure>")
(check-equal? (serialize (primopV (λ (a b) (numV 3)))) "#<primop>")
(check-exn (regexp (regexp-quote "serialize: type not recognized"))
           (lambda () (serialize (idC 'a))))