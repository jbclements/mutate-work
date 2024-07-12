#lang typed/racket

;;> eyeball:6/6, Good

(require typed/rackunit)
(require racket/set)

;; check prim op length

;; Core arith language
(define-type ExprC (U idC ifC appC lamC numV strV))
(struct idC ([s : Symbol]) #:transparent)
(struct ifC ([cond : ExprC] [thn : ExprC] [els : ExprC]) #:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)


;; Value definition
(define-type Value (U numV boolV strV cloV primV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct strV ([str : String]) #:transparent)
(struct primV ([sym : Symbol]) #:transparent)
(struct cloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)

(define PRIM_OPS : (Setof Symbol) (set '+ '- '* '/ '<= 'equal?))
(define PROTECTED_SYMS : (Setof Symbol) (set 'var 'if '-> '=))

;; Environment definitions
(define-type Env (Listof Binding))
(define-type Binding bind)
(struct bind ([name : Symbol] [val : Value]) #:transparent)
(define extend-env cons)
(define mt-env '())
(define top-env (list (bind '+ (primV '+))
                      (bind '- (primV '-))
                      (bind '* (primV '*))
                      (bind '/ (primV '/))
                      (bind '<= (primV '<=))
                      (bind 'equal? (primV 'equal?))
                      (bind 'true (boolV true))
                      (bind 'false (boolV false))))


;; Test variables
(define testSugared2 : Sexp '{var {z = {+ 9 14}}
                                  {y = 98}
                                  {+ z y}})
(define testSexp2 : Sexp '{{{z y} -> {+ z y}}
                           {+ 9 14}
                           98})
(define testSugared : Sexp '{var {f = {{x} -> {+ x 1}}}
                                 {g = {{y} -> {+ y 3}}}
                                 {+ {f 2} {g 4}}})
(define testSexp : Sexp '{{{f g} -> {+ {f 2} {g 4}}}
                                {{x} -> {+ x 1}}
                                {{y} -> {+ y 3}}})
(define testExprC : ExprC
  (appC (lamC (list 'f 'g)
              (appC (idC '+)
                    (list (appC (idC 'f)
                                (list (numV 2)))
                          (appC (idC 'g)
                                (list (numV 4)))))
              )
        (list (lamC (list 'x)
                    (appC (idC '+)
                          (list (idC 'x) (numV 1)))
                    )
              (lamC (list 'y)
                    (appC (idC '+)
                          (list (idC 'y) (numV 3)))
                    )
              )
        )
  )
(define testValue : Value (numV 10))
(define testString : String "10")


;; Desugar helper that extracts function parameters
;; List of Sexp -> List of Symbol
(define (parse-params [args : (Listof Sexp)]) : (Listof Symbol)
  (map (lambda ([exp : Sexp])
         (match exp
           [(list (? symbol? param) '= arg) param]
           [else (error 'ZNQR "Malformatted function: ~e" exp)]))
       args)
  )

(check-equal? (parse-params '{{f = stuf} {g = stuff}}) (list 'f 'g))
(check-exn (regexp (regexp-quote "ZNQR: Malformatted function: '(f stuf)"))
           (lambda () (parse-params '{{f stuf} {g = stuff}})))

;; Desugar helper that extracts function arguments
;; List of Sexp -> List of Sexp
(define (parse-args [args : (Listof Sexp)]) : (Listof Sexp)
  (map (lambda ([exp : Sexp])
         (match exp
           [(list (? symbol? param) '= arg) arg]
           [else (error 'ZNQR "Malformatted function: ~e" exp)]))
       args)
  )
(check-equal? (parse-args '{{f = stuf} {g = stuff}}) (list 'stuf 'stuff))
(check-exn (regexp (regexp-quote "ZNQR: Malformatted function: '(f stuf)"))
           (lambda () (parse-args '{{f stuf} {g = stuff}})))


;; Desugar function
;; Sexp -> Sexp
(define (desugar [exp : Sexp]) : Sexp
  (match exp
    [(list 'var args ...)
     (cons
      (list
       (parse-params (take args (- (length args) 1)))
       '->
       (desugar (last args)))
      (map desugar (parse-args (take args (- (length args) 1)))))
     ]
    [(? list? ls) (map desugar ls)]
    [else exp]
    )
  )

(check-equal? (desugar testSugared) testSexp)
(check-equal? (desugar testSugared2) testSexp2)


;; Parse function that converts Sexp's to core language
;; Sexp -> ExprC
(define (parse [exp : Sexp]) : ExprC
  (match (desugar exp)
    [(? real? n) (numV n)] ; number
    [(? string? str) (strV str)] ; string
    [(? (lambda (sym) (not (set-member? PROTECTED_SYMS sym))) (? symbol? sym))
     (idC sym)] ; identifier
    [(list 'if cond thn els) ; if statement
     (ifC (parse cond) (parse thn) (parse els))]
    [(list (list params ...) '-> body) ; lambda
     (if (and
          (andmap symbol? params)
          (not (ormap (lambda (param) (set-member? PROTECTED_SYMS param)) params))
          ;(not (ormap (lambda (param) (set-member? PRIM_OPS param)) params))
          (not (check-duplicates params))
          )
         (lamC params (parse body))
         (error 'ZNQR "Function variables must be unique unprotected symbols: ~e" params))]
    [(list (? (lambda (sym) (not (set-member? PROTECTED_SYMS sym))) (? symbol? sym)) args ...)
     (if (> (length args) 0)
         (appC (idC sym) (map parse args))
         (appC (idC sym) '()))]
    [(list (list (list params ...) '-> body) args ...) ; application (desugared var)
     (appC (parse (list params '-> body)) (map parse args))]
    [(list body args ...) ; other application
     (appC (parse body) (map parse args))]
    [else (error 'ZNQR "Couldn't parse: ~e" exp)]
    )
  )

(check-equal? (parse 3) (numV 3))
(check-equal? (parse "hello") (strV "hello"))
(check-equal? (parse 'x) (idC 'x))
(check-exn (regexp (regexp-quote "ZNQR: Couldn't parse: '->"))
           (lambda () (parse '->)))
(check-equal? (parse '{if true 2 3}) (ifC (idC 'true) (numV 2) (numV 3)))
(check-equal? (parse '{+ 2 3}) (appC (idC '+) (list (numV 2) (numV 3))))
(check-equal? (parse '{- 2 3}) (appC (idC '-) (list (numV 2) (numV 3))))
(check-equal? (parse '{* 2 3}) (appC (idC '*) (list (numV 2) (numV 3))))
(check-equal? (parse '{/ 2 3}) (appC (idC '/) (list (numV 2) (numV 3))))
(check-equal? (parse '{<= 2 3}) (appC (idC '<=) (list (numV 2) (numV 3))))
(check-equal? (parse '{equal? 2 3}) (appC (idC 'equal?) (list (numV 2) (numV 3))))
(check-equal? (parse '{f 2}) (appC (idC 'f) (list (numV 2))))
(check-equal? (parse '{f}) (appC (idC 'f) '()))
(check-equal? (parse '{{x} -> 5}) (lamC (list 'x) (numV 5)))
;(check-exn (regexp (regexp-quote "ZNQR: Function variables must be unique unprotected symbols: '(+)"))
;           (lambda () (parse '{{+} -> 5})))
(check-exn (regexp (regexp-quote "ZNQR: Function variables must be unique unprotected symbols: '(4)"))
           (lambda () (parse '{{4} -> 5})))
(check-equal? (parse '{{{f} -> 2} {{x} -> 5}})
              (appC (lamC (list 'f) (numV 2)) (list (lamC (list 'x) (numV 5)))))
(check-equal? (parse '{{g} 15}) (appC (appC (idC 'g) '()) (list (numV 15))))
(check-equal? (parse testSexp) testExprC)
(check-equal? (parse '{{var {y = 9} {f 3}}})
              (appC (appC (lamC '(y) (appC (idC 'f) (list (numV 3)))) (list (numV 9))) '()))



;; Primative operator handler
;; Symbol, Value, Value -> Value
(define (primop-handler [primop : Symbol] [a : Value] [b : Value]) : Value
  (match (list primop a b)
    [(list '+ (? numV? l) (? numV? r)) (numV (+ (numV-n l) (numV-n r)))]
    [(list '- (? numV? l) (? numV? r)) (numV (- (numV-n l) (numV-n r)))]
    [(list '* (? numV? l) (? numV? r)) (numV (* (numV-n l) (numV-n r)))]
    [(list '/ (? numV? l) (? (lambda (r) (not (equal? (numV 0) r))) (? numV? r))) (numV (/ (numV-n l) (numV-n r)))]
    [(list '<= (? numV? l) (? numV? r)) (boolV (<= (numV-n l) (numV-n r)))]
    [(list 'equal? l r)
     (boolV
      (and (not (primV? l))
           (not (primV? r))
           (not (cloV? l))
           (not (cloV? r))
           (equal? l r))
      )]
    [else (error 'ZNQR "Cannot apply primative operation ~e to ~e and ~e" primop a b)]
    )
  )

(check-equal? (primop-handler '+ (numV 1) (numV 2)) (numV 3))
(check-equal? (primop-handler '- (numV 1) (numV 2)) (numV -1))
(check-equal? (primop-handler '* (numV 1) (numV 2)) (numV 2))
(check-equal? (primop-handler '/ (numV 2) (numV 1)) (numV 2))
(check-equal? (primop-handler '<= (numV 1) (numV 2)) (boolV true))
(check-equal? (primop-handler '<= (numV 2) (numV 2)) (boolV true))
(check-equal? (primop-handler '<= (numV 3) (numV 2)) (boolV false))
(check-equal? (primop-handler 'equal? (numV 1) (numV 1)) (boolV true))
(check-equal? (primop-handler 'equal? (numV 1) (strV "asdf")) (boolV false))
(check-equal? (primop-handler 'equal? (primV '+) (numV 1)) (boolV false))
(check-equal? (primop-handler 'equal? (numV 1) (primV '+)) (boolV false))
(check-equal? (primop-handler 'equal? (cloV '() (numV 1) '()) (numV 1)) (boolV false))
(check-equal? (primop-handler 'equal? (numV 1) (cloV '() (numV 1) '())) (boolV false))
(check-exn (regexp (regexp-quote "ZNQR: Cannot apply primative operation '+ to (numV 1) and (strV \"asdf\")"))
           (lambda () (primop-handler '+ (numV 1) (strV "asdf"))))
(check-exn (regexp (regexp-quote "ZNQR: Cannot apply primative operation '/ to (numV 1) and (numV 0)"))
           (lambda () (primop-handler '/ (numV 1) (numV 0))))


;; Lookup symbol in the environment
;; Symbol, Env -> Value
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'ZNQR "Failed to lookup: ~e" for)]
    [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
    [else (lookup for (rest env))]
    )
  )

(check-exn (regexp (regexp-quote "ZNQR: Failed to lookup: 'x"))
           (lambda () (lookup 'x top-env)))
(check-equal? (lookup 'x (list (bind 'x (numV 4)))) (numV 4))
(check-equal? (lookup 'x (list (bind 'y (numV 4)) (bind 'x (numV 5)))) (numV 5))


;; Interpreter for ExprC lang
;; ExprC, Env -> Value
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(? numV? val) val]
    [(? strV? val) val]
    [(idC s) (lookup s env)]
    [(? ifC? val)
     (local
       ([define result (interp (ifC-cond val) env)])
       (cond
         [(and (boolV? result) (boolV-b result)) (interp (ifC-thn val) env)]
         [(and (boolV? result) (not (boolV-b result))) (interp (ifC-els val) env)]
         [else (error 'ZNQR "If condition must be a boolV")]
         )
       )
     ]
    [(lamC params body) (cloV params body env)]
    [(appC fun args)
     (match (interp fun env)
       [(primV primop)
        (if (= 2 (length args))
            (primop-handler primop (interp (first args) env) (interp (second args) env))
            (error 'ZNQR "Primative operation must have 2 args got: ~e" (length args))
            )
        ]
       [(cloV params body clo-env)
        (if (= (length params) (length args))
            (interp
             body
             (append
              (map (lambda ([param : Symbol] [arg : ExprC])
                     (bind param (interp arg env)))
                   params args)
              clo-env
              )
             )
            (error 'ZNQR "Wrong number of arguments: got ~e for ~e" (length args) params)
            )
        ]
       [else (error 'ZNQR "Cannot interpret appC: ~e" exp)]
       )
     ]
    )
  )


(check-equal? (interp (numV 1) top-env) (numV 1))
(check-equal? (interp (strV "asdf") top-env) (strV "asdf"))
(check-equal? (interp (idC '+) top-env) (primV '+))
(check-equal? (interp (idC 'x) (extend-env (bind 'x (numV 1)) top-env)) (numV 1))
(check-equal? (interp (ifC (idC 'true) (numV 2) (numV 3)) top-env) (numV 2))
(check-equal? (interp (ifC (idC 'false) (numV 2) (numV 3)) top-env) (numV 3))
(check-exn (regexp (regexp-quote "ZNQR: If condition must be a boolV"))
           (lambda () (interp (ifC (numV 1) (numV 2) (numV 3)) top-env)))
(check-equal? (interp (appC (idC '+) (list (idC 'x) (numV 2))) (extend-env (bind 'x (numV 1)) top-env)) (numV 3))
(check-exn (regexp (regexp-quote "ZNQR: Primative operation must have 2 args got: 1"))
           (lambda () (interp (appC (idC '+) (list (numV 2))) top-env)))
(check-equal? (interp (appC (lamC (list 'x) (idC 'x)) (list (numV 2))) top-env) (numV 2))
(check-equal? (interp (appC (idC 'equal?) (list (strV "hello") (strV "hello"))) top-env) (boolV true))
(check-equal? (interp (appC (idC 'equal?) (list (strV "hello") (strV "world"))) top-env) (boolV false))
(check-equal? (interp testExprC top-env) testValue)
(check-exn (regexp (regexp-quote "ZNQR: Wrong number of arguments: got 2 for '(x)"))
           (lambda () (interp (appC (lamC (list 'x) (idC 'x)) (list (numV 2) (numV 2))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Cannot interpret appC: (appC (numV 3) (list (numV 4) (numV 5)))"))
           (lambda () (interp (appC (numV 3) (list (numV 4) (numV 5))) top-env)))

;; Serialize(string-ify) Values
;; Value -> String
(define (serialize [val : Value]) : String
  (match val
    [(numV n) (~v n)]
    [(boolV b) (if b "true" "false")]
    [(strV s) (~v s)]
    [(primV s) "#<primop>"]
    [(cloV p b e) "#<procedure>"]
    )
  )

(check-equal? (serialize (numV 3)) "3")
(check-equal? (serialize (boolV true)) "true")
(check-equal? (serialize (boolV false)) "false")
(check-equal? (serialize (strV "hello")) "\"hello\"")
(check-equal? (serialize (primV '+)) "#<primop>")
(check-equal? (serialize (cloV '(x) (numV 2) mt-env)) "#<procedure>")


;; Top level interpreter
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

(check-equal? (top-interp testSugared) testString)
