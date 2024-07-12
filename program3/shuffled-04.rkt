#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)

; Language definitions
(define-type ExprC (U IdC AppC LamC NumC BoolC StringC CondC))
(define-type Value (U ClosV NumV PrimV BoolV StringV))
(define-type Env (Immutable-HashTable Symbol Value))

(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct BoolC ([b : Boolean]) #:transparent)
(struct StringC ([str : String]) #:transparent)
(struct CondC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)

(struct ClosV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct NumV ([n : Real]) #:transparent)
(struct PrimV ([s : Symbol]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StringV ([str : String]) #:transparent)

(define reserved-symbols '(var if -> =))

(define top-env : Env (make-immutable-hash
                       (list (cons '+ (PrimV '+))
                             (cons '- (PrimV '-))
                             (cons '* (PrimV '*))
                             (cons '/ (PrimV '/))
                             (cons '<= (PrimV '<=))
                             (cons 'equal? (PrimV 'equal?))
                             (cons 'true (BoolV #t))
                             (cons 'false (BoolV #f)))))

; Evaluate expression, using the list of fundefs to resolve applications
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(NumC n) (NumV n)]
    [(BoolC b) (BoolV b)]
    [(StringC str) (StringV str)]
    [(IdC s)
     (hash-ref env s (λ () (error 'ZNQR "interp: symbol not found: ~e" s)))]
    [(CondC test then else)
     (match (interp test env)
       [(BoolV b) (interp (if b then else) env)]
       [else (error 'ZNQR "interp: conditional test expression must be a boolean")])]
    [(LamC params body) (ClosV params body env)]
    [(AppC fun args)
     (match (interp fun env)
       [(PrimV op) (prim-handler op
                                 (map (λ ([arg : ExprC]) (interp arg env)) args))]
       [(ClosV params body clos-env)
        (interp body
                (extend-env clos-env params
                            (map (λ ([arg : ExprC]) (interp arg env)) args)))]
       [else (error 'ZNQR "interp: value not callable")])]))

; Parse language expressions from S-expressions
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    [(? boolean? b) (BoolC b)]
    [(? string? str) (StringC str)]
    [(? symbol? id) (IdC (assert-not-reserved id))]
    [(list 'if test then else)
     (CondC (parse test) (parse then) (parse else))]
    [(list 'var (list (? symbol? ids) '= exps) ... body)
     (AppC (LamC (assert-no-duplicates
                  (map assert-not-reserved
                          (cast ids (Listof Symbol))))
                 (parse body))
           (map parse (cast exps (Listof Sexp))))]
    [(list (list (? symbol? ids) ...) '-> body)
     (LamC (assert-no-duplicates
            (map assert-not-reserved
                    (cast ids (Listof Symbol))))
           (parse body))]
    [(list fun exps ...)
     (AppC (parse fun) (map parse exps))]
    [else (error 'ZNQR "parse: invalid syntax: ~e" s)]))

; Perform primitive operations
(define (prim-handler [op : Symbol] [args : (Listof Value)]) : Value
  (match (cons op args)
    [(cons '+ (list (NumV n1) (NumV n2))) (NumV (+ n1 n2))]
    [(cons '- (list (NumV n1) (NumV n2))) (NumV (- n1 n2))]
    [(cons '* (list (NumV n1) (NumV n2))) (NumV (* n1 n2))]
    [(cons '/ (list (NumV n1) (NumV n2)))
     (if (zero? n2)
         (error 'ZNQR "prim-handler: division by zero")
         (NumV (/ n1 n2)))]
    [(cons '<= (list (NumV n1) (NumV n2))) (BoolV (<= n1 n2))]
    [(cons 'equal? (list _ _))
     (match args
       [(list (NumV n1) (NumV n2)) (BoolV (equal? n1 n2))]
       [(list (BoolV b1) (BoolV b2)) (BoolV (equal? b1 b2))]
       [(list (StringV str1) (StringV str2)) (BoolV (equal? str1 str2))]
       [else (BoolV #f)])]
    [else (error 'ZNQR "prim-handler: invalid arguments for ~e" op)]))

; Turn values into strings
(define (serialize [v : Value]) : String
  (match v
    [(ClosV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]
    [(BoolV b) (if b "true" "false")]
    [(StringV str) (~v str)]
    [(NumV n) (~v n)]))

; Parse and evaluate ZNQR3 code
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; Add values to an environment
(define (extend-env [env : Env] [s : (Listof Symbol)] [v : (Listof Value)]) : Env
  (match (cons s v)
    [(cons '() '()) env]
    [(cons (list _ _ ...) (list _ _ ...))
     (extend-env (hash-set env (first s) (first v)) (rest s) (rest v))]
    [else (error 'ZNQR "extend-env: mismatching argument/parameter count")]))

; Throw an error if there are duplicate symbols in a list, otherwise return list
(define (assert-no-duplicates [s : (Listof Symbol)]) : (Listof Symbol)
  (if (equal? (check-duplicates s) #f) s
      (error 'ZNQR "parse: duplicate symbol")))

; Throw an error if the symbol is reserved, otherwise return symbol
(define (assert-not-reserved [s : Symbol]) : Symbol
  (if (member s reserved-symbols)
      (error 'ZNQR "parse: illegal use of reserved symbol: ~e" s) s))


;;;;; Test Cases ;;;;;

; interp
(check-equal? (interp (NumC 0) top-env) (NumV 0))
(check-equal? (interp (BoolC #t) top-env) (BoolV #t))
(check-equal? (interp (StringC "hi") top-env) (StringV "hi"))
(check-equal? (interp (IdC '+) top-env) (PrimV '+))
(check-equal? (interp (CondC (BoolC #t) (NumC 0) (NumC 1)) top-env) (NumV 0))
(check-equal? (interp (CondC (BoolC #f) (NumC 0) (NumC 1)) top-env) (NumV 1))
(check-equal? (interp (LamC '(a b) (IdC 'a)) top-env)
              (ClosV '(a b) (IdC 'a) top-env))
(check-equal? (interp (AppC (IdC '+) (list (NumC 1) (NumC 2))) top-env) (NumV 3))
(check-equal? (interp (AppC (LamC '(a b) (IdC 'a)) (list (NumC 1) (NumC 2))) top-env) (NumV 1))
(check-exn (regexp (regexp-quote "ZNQR: interp: symbol not found: 'f"))
           (λ () (interp (IdC 'f) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: interp: conditional test expression must be a boolean"))
           (λ () (interp (CondC (NumC 0) (NumC 0) (NumC 0)) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: interp: value not callable"))
           (λ () (interp (AppC (NumC 0) '()) top-env)))

; parse
(check-equal? (parse 1)(NumC 1))
(check-equal? (parse #t) (BoolC #t))
(check-equal? (parse "hi") (StringC "hi"))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '{if true 0 1})
              (CondC (IdC 'true) (NumC 0) (NumC 1)))
(check-equal? (parse '{var 2})
              (AppC (LamC '() (NumC 2)) '()))
(check-equal? (parse '{var {x = 0} {y = 1} 2})
              (AppC (LamC '(x y) (NumC 2)) (list (NumC 0) (NumC 1))))
(check-equal? (parse '{f 0 1})
              (AppC (IdC 'f) (list (NumC 0) (NumC 1))))
(check-equal? (parse '{{a b c} -> 0})
              (LamC '(a b c) (NumC 0)))
(check-exn (regexp (regexp-quote "ZNQR: parse: illegal use of reserved symbol: '="))
           (λ () (parse '=)))
(check-exn (regexp (regexp-quote "ZNQR: parse: invalid syntax: '()"))
           (λ () (parse '{})))

; prim-handler
(check-equal? (prim-handler '+ (list (NumV 1) (NumV 2))) (NumV 3))
(check-equal? (prim-handler '- (list (NumV 1) (NumV 2))) (NumV -1))
(check-equal? (prim-handler '* (list (NumV 2) (NumV 3))) (NumV 6))
(check-equal? (prim-handler '/ (list (NumV 6) (NumV 3))) (NumV 2))
(check-equal? (prim-handler '<= (list (NumV 0) (NumV 1))) (BoolV #t))
(check-equal? (prim-handler 'equal? (list (NumV 0) (NumV 0))) (BoolV #t))
(check-equal? (prim-handler 'equal? (list (BoolV #t) (BoolV #t))) (BoolV #t))
(check-equal? (prim-handler 'equal? (list (StringV "hi") (StringV "hi"))) (BoolV #t))
(check-equal? (prim-handler 'equal? (list (NumV 0) (StringV "hi"))) (BoolV #f))
(check-exn (regexp (regexp-quote "ZNQR: prim-handler: division by zero"))
           (λ () (prim-handler '/ (list (NumV 1) (NumV 0)))))
(check-exn (regexp (regexp-quote "ZNQR: prim-handler: invalid arguments for '+"))
           (λ () (prim-handler '+ (list (BoolV #t) (BoolV #t)))))

; serialize
(check-equal? (serialize (NumV 1)) "1")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (StringV "hi")) "\"hi\"")
(check-equal? (serialize (ClosV '() (NumC 0) (hash))) "#<procedure>")

; top-interp
(check-equal? (top-interp '{+ 1 2}) "3")
(check-equal? (top-interp '{var {+ = true}
                                {- = false}
                                {is-half? = {{x y} -> {equal? {* x 2} y}}}
                                {if {equal? + {is-half? 3 6}}
                                    "yes"
                                    "no"}}) "\"yes\"")

; extend-env
(check-equal? (extend-env (hash) '(a b) (list (NumV 0) (NumV 1)))
              (make-immutable-hash
               (list
                (cons 'a (NumV 0))
                (cons 'b (NumV 1)))))
(check-exn (regexp (regexp-quote "ZNQR: extend-env: mismatching argument/parameter count"))
           (λ () (extend-env (hash) '(a b) '())))

; assert-no-duplicates
(check-equal? (assert-no-duplicates '(a b c)) '(a b c))
(check-exn (regexp (regexp-quote "ZNQR: parse: duplicate symbol"))
           (λ () (assert-no-duplicates '(a b b))))

; assert-not-reserved
(check-equal? (assert-not-reserved 'a) 'a)
(check-exn (regexp (regexp-quote "ZNQR: parse: illegal use of reserved symbol: '="))
           (λ () (assert-not-reserved '=)))

