#lang typed/racket
(require typed/rackunit)

;; description of ExprC
(define-type ExprC (U num  ifleq0 appC idC lamC))
(struct num([n : Real]) #:transparent)
(struct ifleq0([test : ExprC][then : ExprC][else : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

;; description of Value
(define-type Value (U Real Boolean closV primV))
(struct closV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primV ([binop : (Real Real -> Real)]) #:transparent)

;; interp stuff
(struct Binding ((name : Symbol) (val : Value)) #:transparent)
(define-type Env (Listof Binding))
(define extend-env cons)
(define mt-env (list (Binding 'true #t)
                      (Binding 'false #f)
                      (Binding '+ (primV +))
                      (Binding '- (primV -))
                      (Binding '* (primV *))
                      (Binding '/ (primV /))
                      ))

;; lookup finds the value of a symbol in the environment
(: lookup : Symbol Env -> Value)
(define (lookup for env)
  (cond
    [(empty? env) (error "ZNQR: name not found")]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (Binding-val (first env))]
            [else (lookup for (rest env))])]))
;; lookup-bool returns true if the symbol is in the env and false otherwise
(: lookup-bool : Symbol Env -> Value)
(define (lookup-bool for env)
  (cond
    [(empty? env) #f]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             #t]
            [else (lookup for (rest env))])]))
;; lookup tests
(check-exn (regexp (regexp-quote  "ZNQR: name not found"))
           (lambda () (lookup 'p (list))))

;; serialize returns a string
(: serialize : Value -> String)
(define (serialize val)
  (match val
    [(? real?) (~v val)]
    [(? boolean?) (cond [val "true"] [else "false"])]
    [(? closV?) "#<procedure>"]
    [(? primV?) "#<primop>"]))
;; test for serialize
(check-equal? (serialize 5) "5")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (closV (list 'f) (num 5) (list))) "#<procedure>")
(check-equal? (serialize (primV +)) "#<primop>")

;; interp: evaluates the given ExprC
(: interp : ExprC Env -> Value)
(define (interp expr env)
  (match expr
    [(num n) n]
    [(ifleq0 test then rest) (if (<= (cast (interp test env) Real) 0)
                                 (interp then env)
                                 (interp rest env))]
    ;; for appC, args is a list of exprC
    [(appC f args) (match (interp f env)
                                 [(primV op) (map (lambda ([x : ExprC]) (interp x env)))]
                                 [(closV clargs body env) (interp body (foldl
                                                        (lambda
                                                            ([actualArg : ExprC]
                                                             [formalArg : Symbol] [result : (Listof Binding)])
                                                          (extend-env
                                                           (Binding formalArg
                                                                    (cast (interp actualArg env) Real)) result))
                                                        env args clargs))])]
    [(idC n) (lookup n env)]
    [(lamC args body) (closV args body env)]))

;; tests for new interp
(check-equal? (interp (appC '+ (list (num 5) (num 6))) '()) 11)
;;(check-equal? (interp (appC (idC 'f) (list (num 5) (num 6)))
;;                      (list (Binding 'g 5) (Binding 'a 5)
;;                            (Binding 'f (closV (list 'a 'b) (appC (idC '+) (idC 'a) (idC 'b)) '())))) 11)
;;(check-exn (regexp (regexp-quote  "ZNQR: division by 0"))
;;           (lambda () (interp ('/ (num 5) (num 0)) '())))
(check-equal? (interp (ifleq0 (num 5) (num 6) (num 7)) '()) 7)
(check-equal? (interp (ifleq0 (num -4) (num 6) (num 7)) '()) 6)
