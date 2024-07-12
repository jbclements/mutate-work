#lang typed/racket

;;> eyeball: 6/6, Good. See comment

(require typed/rackunit)

; ===============================================================
; Summary

; I finished! I was stuck on a really long test case that deals
; with the ClosV environment vs the other environment, but eventually
; figured it out. I'm super happy now.

; ===============================================================
; Expression & Function Definitions

; ExprC
(define-type ExprC (U NumC StringC IdC AppC IfC LamC))
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([str : String]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct IfC ([exp1 : ExprC] [exp2 : ExprC] [exp3 : ExprC]) #:transparent)

; Value
(define-type Value (U NumV BoolV StringV ClosV PrimV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([val : Boolean]) #:transparent)
(struct StringV ([val : String]) #:transparent)
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([op : Symbol]))

; Env
(define-type Env (Immutable-HashTable Symbol Value))

; =================================================================
; Interpreter

; Accepts an s-expression and returns a serialized Value.
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-level-env)))

; Evaluates an expression using a given environment and
; returns a Value.
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(NumC n) (NumV n)]
    [(StringC str) (StringV str)]
    [(IdC x) (id-lookup x env)]
    [(IfC exp1 exp2 exp3)
     (conditional (interp exp1 env) exp2 exp3 env)]
    [(AppC fun args)
     (match (interp fun env)
       [(PrimV op) (prim-handler op (interp-args args env))]
       [(ClosV clo-args body clo-env)
        (cond
          [(not (= (length clo-args) (length args)))
           (error 'ZNQR "Wrong number of arguments passed to function")]
          [else
           (interp body (extend-env-with-list clo-args args env clo-env))])
        ]
       [_ (error 'ZNQR "Invalid function call")]
       )]
    [(LamC args body) (ClosV args body env)]
    ;;> bring trailing parens up
    ))

; Looks in an Env (hash) for a specific symbol and returns the value.
(define (id-lookup [sym : Symbol] [env : Env]): Value
  (hash-ref env sym
            (λ () (error 'ZNQR "Id not found: ~e" sym))))

; Accepts an env, param, and val and returns a new environment
; that includes the param and val as a key-value pair.
(define (extend-env [env : Env] [param : Symbol] [val : Value]) : Env
  (hash-set env param val))

; Accepts an env, a list of params and a list of args and
; adds each pair to a given environment.
(define (extend-env-with-list [clo-args : (Listof Symbol)] [args : (Listof ExprC)] [env : Env] [clo-env : Env]) : Env
  (cond
    [(empty? clo-args) clo-env]
    [else
     (cast args (Listof ExprC))
     (define new-env (extend-env clo-env (first clo-args) (interp (first args) env)))
     (extend-env-with-list (rest clo-args) (rest args) env new-env)]))

; Accepts a symbol and a list of args (Values) and computes
; the args using the symbol as the operand.
(define (prim-handler [op : Symbol] [args : (Listof Value)]) : Value
  (match args
    [(list (? NumV? num1) (? NumV? num2))
     (prim-binop-handler op (NumV-n num1) (NumV-n num2))]
    [(list b1 b2)
     (match op
       ['equal? (BoolV (equal? b1 b2))]
       [_ (error 'ZNQR "Invalid argument types supplied to ~e" op)])]
    ))

; Accepts an op symbol and two numbers. Attempts to evaluate the numbers
; and throws an error if anything is wrong.
(define (prim-binop-handler [op : Symbol] [n1 : Real] [n2 : Real]) : Value
  (match op
    ['+ (NumV (+ n1 n2))]
    ['- (NumV (- n1 n2))]
    ['* (NumV (* n1 n2))]
    ['/ (if (= n2 0)
            (error 'ZNQR "Divide by zero error")
            (NumV (/ n1 n2)))]
    ['<= (BoolV (<= n1 n2))]
    ['equal? (BoolV (equal? n1 n2))]))

; Accepts a list of args and returns a list of interpreted args.
; The new list will be a list of Values.
(define (interp-args [args : (Listof ExprC)] [env : Env]) : (Listof Value)
  (map (λ ([arg : ExprC])
         (interp arg env)) args))

; Checks the first value and returns v2 if true, v3 if false,
; or errors if the first value isn't a boolean.
(define (conditional [v1 : Value] [exp1 : ExprC] [exp2 : ExprC] [env : Env]) : Value
  (match v1
    [(BoolV b)
     (if b (interp exp1 env) (interp exp2 env))]
    [_ (error 'ZNQR "First arg in if statement isn't a boolean")]))

; Accepts any Value and returns a serialized string of that Value.
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (~v n)]
    [(StringV str) str]
    [(BoolV v) (if (equal? v #t) "true" "false")]
    [(ClosV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]))

; Top-level environment.
(define top-level-env : Env
  (make-immutable-hash
   (list (cons '+ (PrimV '+))
         (cons '- (PrimV '-))
         (cons '* (PrimV '*))
         (cons '/ (PrimV '/))
         (cons '<= (PrimV '<=))
         (cons 'equal? (PrimV 'equal?))
         (cons 'true (BoolV #t))
         (cons 'false (BoolV #f)))))

; ===============================================================
; Parser

; Accepts an ExprC s-expression and converts it into ExprC syntax.
(define (parse [s : Sexp]) : ExprC
  (match s
    [(list 'var (list (? symbol? args) '= body) ... sexps)
     (AppC (LamC (test-args (cast args (Listof Symbol))) (parse sexps))
           (map parse (cast body (Listof Sexp))))]
    [(? real? n) (NumC n)]
    [(? string? str) (StringC str)]
    [(? symbol? sym)
     (IdC (test-symbol sym))]
    [(list 'if exp1 exp2 exp3)
     (IfC (parse exp1) (parse exp2) (parse exp3))]
    [(list (list (? symbol? args) ...) '-> body)
     (LamC (test-args (cast args (Listof Symbol))) (parse body))]
    [(list (list bad-args ...) '-> body) (error 'ZNQR "Arguments must be symbols")]
    [(list sexps ...)
     (AppC (parse (first sexps)) (map parse (rest sexps)))]
    ))

; Checks if a symbol is reserved and throws an error, or returns the symbol.
(define (test-symbol [sym : Symbol]) : Symbol
  (cond
    [(hash-has-key? reserved-ids sym)
     (error 'ZNQR "Reserved symbol used")]
    [else sym]))

; Checks for duplicate args and reserved symbols. If no errors are found,
; returns the original list.
(define (test-args [args : (Listof Symbol)]) : (Listof Symbol)
  (cond
    [(not (not (check-duplicates args)))
     (error 'ZNQR "Duplicate argument found")]
    [else (map test-symbol args)]
    ))

; Hash table that contains reserved symbols.
(define reserved-ids
  (make-immutable-hash
   '((var #t) (if #t) (or #t) (= #t) (-> #t))))

; ===============================================================
; Tests

; = Interpreter Tests

(check-exn (regexp (regexp-quote "ZNQR: Invalid function call"))
           (lambda () (top-interp '(3 4 5))))

(check-exn (regexp (regexp-quote "ZNQR: Divide by zero error"))
           (lambda () (top-interp '(/ 1 (- 3 3)))))

(check-exn (regexp (regexp-quote "ZNQR: Invalid argument types supplied to '+"))
           (lambda () (top-interp '(+ + +))))

(check-exn (regexp (regexp-quote "ZNQR: Wrong number of arguments passed to function"))
           (lambda () (top-interp '((() -> 9) 17))))

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{x} -> {/ x 2}}}) "2")

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{x} -> {<= x 2}}}) "false")

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{x} -> {equal? x 4}}}) "true")

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{x} -> {equal? x true}}}) "false")

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{x} -> "hello"}}) "hello")

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{g} -> {if {<= {- 0 1} 1} {* 2 12} 555}}}) "24")

(check-equal? (top-interp '{{{f} -> {f 4}}
         {{x} -> {if false x 555}}}) "555")

(check-equal? (top-interp '{{{f g} -> {+ {f 2} {g 9}}}
          {{x} -> {+ x 1}}
          {{z} -> {+ z 2}}}) "14")

(check-exn (regexp (regexp-quote "ZNQR: First arg in if statement isn't a boolean"))
           (lambda () (conditional (NumV 2) (NumC 1) (NumC 3) top-level-env)))

(check-equal? (top-interp '{{a} -> 3}) "#<procedure>")

(check-exn (regexp (regexp-quote "ZNQR: Id not found: 'x"))
           (lambda () (id-lookup 'x top-level-env)))

(check-equal? (serialize (NumV 34)) "34")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (ClosV (list 'x) (NumC 3) top-level-env)) "#<procedure>")
(check-equal? (serialize (PrimV '+)) "#<primop>")

; = Parser Tests

(check-exn (regexp (regexp-quote "ZNQR: Arguments must be symbols"))
           (lambda () (parse '((3 4 5) -> 6))))

(check-exn (regexp (regexp-quote "ZNQR: Duplicate argument found"))
           (lambda () (parse '((x x) -> 3))))

(check-exn (regexp (regexp-quote "ZNQR: Reserved symbol used"))
           (lambda () (parse '(+ if var))))


(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}})
              (AppC (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))

(check-equal? (parse '{{x y} -> {+ x 2}})
              (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (NumC 2)))))

(check-equal?
 (parse '{{{f} -> {f 4}}
         {{x} -> {+ x 2}}})
 (AppC (LamC '(f) (AppC (IdC 'f) (list (NumC 4))))
       (list (LamC '(x) (AppC (IdC '+) (list (IdC 'x) (NumC 2)))))))
