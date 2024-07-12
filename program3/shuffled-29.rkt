#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)
; progress: fully completed asgn3

; type definitions for ExprC
(define-type ExprC (U NumC IdC AppC StringC LamC))
(struct NumC ([n : Real])#:transparent)
(struct AppC ([fn : ExprC]
              [arg : (Listof ExprC)])#:transparent)
(struct IdC ([s : Symbol])#:transparent)
(struct StringC ([str : String])#:transparent)
(struct LamC ([arg : (Listof Symbol)] [body : ExprC])#:transparent)

; type definitions for Values
(define-type Value (U NumV BoolV StringV PrimV CloV))
(struct NumV ([n : Real])#:transparent)
(struct BoolV ([boo : Boolean])#:transparent)
(struct StringV ([str : String])#:transparent)
(struct PrimV ([op : Symbol])#:transparent)
(struct CloV ([arg : (Listof Symbol)] [body : ExprC] [env : Env])#:transparent)

; hashtable for top-env
(define-type Env (Immutable-HashTable Symbol Value))
(define top-env (make-immutable-hash
                 (list (cons '+ (PrimV '+))
                       (cons '- (PrimV '-))
                       (cons '* (PrimV '*))
                       (cons '/ (PrimV '/))
                       (cons '<= (PrimV '<=))
                       (cons 'equal? (PrimV 'equal?))
                       (cons 'if (PrimV 'if))
                       (cons 'true (BoolV #true))
                       (cons 'false (BoolV #false)))))

; top-interp accepts an s-expression, calls the parser and
; the desugar function and then the interp function
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; serialize accepts any ZNQR3 value and
; returns the serialized version of said value
(define (serialize [v : Value]) : String
  (match v
    [(NumV n) (~v n)]
    [(StringV s) (~v s)]
    [(BoolV boo) (match boo
                   [#t "true"]
                   [else "false"])]
    [(PrimV op) "#<primop>"]
    [(CloV arg body env) "#<procedure>"]))

; interp takes an ExprC and an environment
; and returns the evaluated value
(define (interp [a : ExprC] [env : Env]) : Value
  (match a
    [(NumC n) (NumV n)]
    [(StringC str) (StringV str)]
    [(IdC s) (if (hash-has-key? env s)
                 (hash-ref env s)
                 (error 'interp "ZNQR: id not found ~e" s))]
    [(AppC fn args) (match (interp fn env)
                      [(PrimV op) (match op
                                    ['if (match (interp (first args) env)
                                               [(BoolV boo) (if boo
                                                                (interp (first (rest args)) env)
                                                                (interp (first (rest (rest args))) env))]
                                               [else (error 'interp "ZNQR: conditional with non-boolean test")])]
                                    [else (prim-handler op (map (λ ([arg : ExprC]) (interp arg env)) args))])]
                      [(CloV param body clo-env)
                       (cond
                         [(equal? (length args) (length param))
                          (define new-env (extend-env clo-env param
                                                           (map (λ ([arg : ExprC])
                                                                  (interp arg env)) args)))
                               (interp body new-env)]
                         [else (error 'interp "ZNQR: applying function to wrong num of args")])]
                      [else (error 'interp "ZNQR: application of non-closure or primitive")])]
    [(LamC args body) (CloV args body env)]))

; prim-handler handles all of the primitive operations
; it accepts an operation and a value and returns the
; interpreted primitive operation value
(define (prim-handler [op : Symbol] [v : (Listof Value)]) : Value
  (match op
    ['+ (prim-add (first v) (first (rest v)))]
    ['- (prim-sub (first v) (first (rest v)))]
    ['* (prim-mult (first v) (first (rest v)))]
    ['/ (prim-div (first v) (first (rest v)))]
    ['<= (prim-lte? (first v) (first (rest v)))]
    ['equal? (prim-equal? (first v) (first (rest v)))]))

; prim-add accepts two real values and computes
; a + b. it signals an error if either a/b are
; not a number
(define (prim-add [a : Value] [b : Value]) : Value
  (cond
    [(and (NumV? a) (NumV? b)) (NumV (+ (NumV-n a) (NumV-n b)))]
    [else (error 'prim-add "ZNQR: must add numbers only")]))

; prim-sub accepts two real values and computes
; a - b. it signals an error if either a/b are
; not a number
(define (prim-sub [a : Value] [b : Value]) : Value
  (cond
    [(and (NumV? a) (NumV? b)) (NumV (- (NumV-n a) (NumV-n b)))]
    [else (error 'prim-sub "ZNQR: must subtract numbers only")]))

; prim-mult accepts two real values and computes
; a * b. it signals an error if either a/b are
; not a number
(define (prim-mult [a : Value] [b : Value]) : Value
  (cond
    [(and (NumV? a) (NumV? b)) (NumV (* (NumV-n a) (NumV-n b)))]
    [else (error 'prim-mult "ZNQR: must multiply numbers only")]))

; prim-div accepts two real values and computes
; a / b. it signals an error if either a/b are
; not a number or if b is zero
(define (prim-div [a : Value] [b : Value]) : Value
  (cond
    [(and (and (NumV? a) (NumV? b)) (positive? (NumV-n b))) (NumV (/ (NumV-n a) (NumV-n b)))]
    [(and (and (NumV? a) (NumV? b)) (zero? (NumV-n b))) (error 'prim-div "ZNQR: cannot divide by zero")]
    [else (error 'prim-div "ZNQR: must divide numbers only")]))

; prim-lte accepts two real values and returns
; true if a <= b. it signals an error if either
; a/b are not a number
(define (prim-lte? [a : Value] [b : Value]) : Value
  (cond
    [(and (and (NumV? a) (NumV? b)) (<= (NumV-n a) (NumV-n b))) (BoolV #true)]
    [(and (and (NumV? a) (NumV? b)) (> (NumV-n a) (NumV-n b))) (BoolV #false)]
    [else (error 'prim-lte? "ZNQR: must input numbers only for <=")]))

; prim-equal? accepts two real values and returns
; true if neither value is a closure or a primop
; and the two values are equal. no error signals.
(define (prim-equal? [a : Value] [b : Value]) : Value
  (cond
    [(and (and (NumV? a) (NumV? b)) (equal? (NumV-n a) (NumV-n b))) (BoolV #true)]
    [(and (and (StringV? a) (StringV? b)) (equal? (StringV-str a) (StringV-str b))) (BoolV #true)]
    [(and (and (BoolV? a) (BoolV? b)) (equal? (BoolV-boo a) (BoolV-boo b))) (BoolV #true)]
    [else (BoolV #false)]))

; extend-env accepts an environment, parameters and list of values
; and extends the environment by using hash-set
(define (extend-env [env : Env] [param : (Listof Symbol)] [v : (Listof Value)]) : Env
  (cond
    [(and (empty? param) (empty? v)) env]
    [else
     (define setting (hash-set env (first param) (first v)))
     (extend-env setting (rest param) (rest v))]))

; parse maps an Sexp to an ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? s) (NumC s)]
    [(? symbol? s) (match s
                     [(or 'var 'if '-> '=)
                      (error 'parse "ZNQR: IdC cannot be a reserved symbol")]
                     [else (IdC s)])]
    [(? string? s) (StringC s)]
    [(list 'if exprs ...) (cond
                            [(equal? (length exprs) 3)
                             (AppC (IdC 'if) (list (parse (first exprs))
                                                   (parse (first (rest exprs)))
                                                   (parse (first (rest (rest exprs))))))]
                            [else (error 'parse "ZNQR: check arity of ifleq0")])]
    [(list (list (? symbol? args) ...) '-> expr) (if (args-same-name? (cast args (Listof Symbol)))
                                                     (error 'parse "ZNQR: duplicate function arguments")
                                                     (LamC (cast args (Listof Symbol)) (parse expr)))]
    [(list 'var args ... body) (cond
                                 [(args-same-name? (return-ids (cast args Sexp)))
                                   (error 'parse "ZNQR: duplicate function arguments")]
                                   [else (desugar s)])]
    [(list (? symbol? fn) exprs ...) #:when (hash-has-key? top-env fn)
                                     (cond
                                       [(equal? (length exprs) 2)
                                        (AppC (IdC fn) (list (parse (first exprs))
                                                             (parse (first (rest exprs)))))]
                                       [else (error 'parse "ZNQR: check arity of binop")])]
    [(list fn args ...) (AppC (parse fn) (map (λ ([arg : Sexp]) (parse arg)) args))]
    [else (error 'parse "ZNQR: check parse input")]))

; args-same-name? accepts a list of symbols and
; returns true if the function arguments
; have the same name (if theres duplicates)
(define (args-same-name? [l : (Listof Symbol)]) : Boolean
  (cond
    [(empty? l) #false]
    [else (or (ormap (λ ([arg : Symbol]) (equal? (first l) arg)) (rest l))
         (args-same-name? (rest l)))]))

; desugar accepts an sexp and returns
; the desugared var form
(define (desugar [s : Sexp]) : ExprC
  (match s
    [(list 'var args ... body)
     (define ids (return-ids (cast args Sexp)))
     (define exprs (return-exprs (cast args Sexp)))
     (AppC (LamC ids (parse body)) exprs)]))

; return-ids iterates through variable definitions
; and returns variable identifiers
(define (return-ids [s : Sexp]) : (Listof Symbol)
  (match s
    [(? empty? s) '()]
    [(list (list (? symbol? id) '= expr) vars ...) (cond
                                                     [(equal? '-> id)
                                                      (error 'return-ids "ZNQR: invalid variable name")]
                                                     [(equal? 'if id)
                                                      (error 'return-ids "ZNQR: invalid variable name")]
                                                     [(equal? '= id)
                                                      (error 'return-ids "ZNQR: invalid variable name")]
                                                     [(equal? 'var id)
                                                      (error 'return-ids "ZNQR: invalid variable name")]
                                                     [else (cons id (return-ids vars))])]))

; return-exprs iterates through variable definitions
; and returns variable expressions
(define (return-exprs [s : Sexp]) : (Listof ExprC)
  (match s
    [(? empty? s) '()]
    [(list (list (? symbol? id) '= expr) vars ...) (cons (parse expr) (return-exprs vars))]))

; TESTING
; testing top-interp
(check-equal? (top-interp '(+ 1 2)) "3")
(check-equal? (top-interp '(- 10 2)) "8")
(check-equal? (top-interp '(* 1 2)) "2")
(check-equal? (top-interp '(/ 10 2)) "5")
(check-equal? (top-interp '{{} -> 9}) "#<procedure>")
(check-equal? (top-interp '(if (equal? 10 10) true false)) "true")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {+ z y}})
              "121")
(check-equal? (top-interp '{{{z y} -> {+ z y}}
                            {+ 9 14}
                            98})
              "121")
(check-exn #px"ZNQR: cannot divide by zero"
           (λ () (top-interp '(/ 5 0))))
(check-exn #px"ZNQR: applying function to wrong num of args"
           (λ () (top-interp '((() -> 9) 17))))

; testing serialize
(check-equal? (serialize (NumV 2)) "2")
(check-equal? (serialize (StringV "howdy")) "\"howdy\"")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (CloV '() (NumC 10) top-env)) "#<procedure>")

; testing interp
(check-equal? (interp (NumC 10) top-env) (NumV 10))
(check-equal? (interp (StringC "howdy") top-env) (StringV "howdy"))
(check-equal? (interp (IdC '+) top-env) (PrimV '+))
(check-exn #px"ZNQR: id not found"
           (λ ()
             (interp (IdC '%) top-env)))
(check-equal? (interp (AppC (IdC '+) (list (NumC 1) (NumC 2))) top-env)
              (NumV 3))
(check-equal? (interp (AppC (IdC '-) (list (NumC 2) (NumC 2))) top-env)
              (NumV 0))
(check-equal? (interp (AppC (IdC '/) (list (NumC 2) (NumC 2))) top-env)
              (NumV 1))
(check-equal? (interp (AppC (IdC '*) (list (NumC 1) (NumC 2))) top-env)
              (NumV 2))
(check-equal? (interp (AppC (IdC '<=) (list (NumC 1) (NumC 2))) top-env)
              (BoolV #true))
(check-equal? (interp (AppC (IdC '<=) (list (NumC 5) (NumC 2))) top-env)
              (BoolV #false))
(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 1) (NumC 1))) top-env)
              (BoolV #true))
(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 1) (NumC 2))) top-env)
              (BoolV #false))
(check-equal? (interp (AppC (IdC 'if)
                            (list (AppC (IdC 'equal?)
                                        (list (NumC 10) (NumC 5)))
                                  (IdC 'true)
                                  (IdC 'false))) top-env)
              (BoolV #false))
(check-equal? (interp (AppC (IdC 'if)
                            (list (AppC (IdC 'equal?)
                                        (list (NumC 10) (NumC 10)))
                                  (IdC 'true)
                                  (IdC 'false))) top-env)
              (BoolV #true))
(check-exn #px"ZNQR: conditional with non-boolean test"
           (λ ()
             (interp (AppC (IdC 'if) (list (NumC 1) (NumC 1) (NumC 1))) top-env)))
(check-equal? (interp (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y)))) top-env)
              (CloV (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))) top-env))
(check-exn #px"ZNQR: application of non-closure or primitive"
           (λ ()
             (interp (AppC (NumC 10) (list (NumC 10) (NumC 1))) top-env)))

; testing prim-add
(check-equal? (prim-add (NumV 1) (NumV 2)) (NumV 3))
(check-exn #px"ZNQR: must add numbers only"
           (λ ()
             (prim-add (NumV 1) (BoolV #true))))

; testing prim-sub
(check-equal? (prim-sub (NumV 10) (NumV 2)) (NumV 8))
(check-exn #px"ZNQR: must subtract numbers only"
           (λ ()
             (prim-sub (NumV 10) (BoolV #true))))

; testing prim-mult
(check-equal? (prim-mult (NumV 10) (NumV 2)) (NumV 20))
(check-exn #px"ZNQR: must multiply numbers only"
           (λ ()
             (prim-mult (NumV 10) (BoolV #true))))

; testing prim-div
(check-equal? (prim-div (NumV 10) (NumV 2)) (NumV 5))
(check-exn #px"ZNQR: cannot divide by zero"
           (λ ()
             (prim-div (NumV 10) (NumV 0))))
(check-exn #px"ZNQR: must divide numbers only"
           (λ ()
             (prim-div (NumV 10) (BoolV #true))))

; testing prim-lte
(check-equal? (prim-lte? (NumV 10) (NumV 20)) (BoolV #true))
(check-equal? (prim-lte? (NumV 20) (NumV 10)) (BoolV #false))
(check-exn #px"ZNQR: must input numbers only for <="
           (λ ()
             (prim-lte? (NumV 10) (BoolV #true))))

; testing prim-equal?
(check-equal? (prim-equal? (NumV 10) (NumV 10)) (BoolV #true))
(check-equal? (prim-equal? (NumV 20) (NumV 10)) (BoolV #false))
(check-equal? (prim-equal? (BoolV #true) (BoolV #true)) (BoolV #true))
(check-equal? (prim-equal? (StringV "howdy") (StringV "howdy")) (BoolV #true))
(check-equal? (prim-equal? (PrimV '+) (PrimV '+)) (BoolV #false))

; testing args-same-name?
(check-equal? (args-same-name? '{a b}) #false)
(check-equal? (args-same-name? '{x x}) #true)
(check-equal? (args-same-name? (return-ids '{{z = {+ 9 14}} {z = 98}})) #true)

; testing extend-env
(define testing-env (make-immutable-hash (list)))
(define expected-env (make-immutable-hash
                      (list (cons 'x (NumV 1))
                            (cons 'y (NumV 2)))))
(check-equal? (extend-env testing-env (list 'x 'y) (list (NumV 1) (NumV 2))) expected-env)

; testing parse
(check-equal? (parse 2) (NumC 2))
(check-equal? (parse 200) (NumC 200))
(check-equal? (parse "howdy") (StringC "howdy"))
(check-equal? (parse '(+ 1 2)) (AppC (IdC '+) (list (NumC 1) (NumC 2))))
(check-equal? (parse '(+ 10 10)) (AppC (IdC '+) (list (NumC 10) (NumC 10))))
(check-equal? (parse '(* 1 2)) (AppC (IdC '*) (list (NumC 1) (NumC 2))))
(check-equal? (parse '(* 10 10)) (AppC (IdC '*) (list (NumC 10) (NumC 10))))
(check-equal? (parse '(- 1 2)) (AppC (IdC '-) (list (NumC 1) (NumC 2))))
(check-equal? (parse '(- 10 10)) (AppC (IdC '-) (list (NumC 10) (NumC 10))))
(check-equal? (parse '(/ 20 10)) (AppC (IdC '/) (list (NumC 20) (NumC 10))))
(check-equal? (parse '(/ 300 2)) (AppC (IdC '/) (list (NumC 300) (NumC 2))))
(check-equal? (parse '(if (equal? 10 5) true false)) (AppC (IdC 'if)
                                                           (list (AppC (IdC 'equal?)
                                                                       (list (NumC 10) (NumC 5)))
                                                                 (IdC 'true)
                                                                 (IdC 'false))))
(check-equal? (parse '{{z y} -> {+ z y}})
                     (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y)))))
(check-equal? (parse '{{{z y} -> {+ z y}} {+ 9 14} 98})
                     (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                           (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}})
              (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                           (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-exn #px"ZNQR: check arity of binop"
           (λ () (parse '(+ 1 2 3))))
(check-exn #px"ZNQR: check arity of binop"
           (λ () (parse '(+ 1))))
(check-exn #px"ZNQR: check arity of if"
           (λ () (parse '(if 1 1))))
(check-exn #px"ZNQR: check arity of if"
           (λ () (parse '(if 1))))
(check-exn #px"ZNQR: IdC cannot be a reserved symbol"
           (λ () (parse '->)))
(check-exn #px"ZNQR: check parse input"
           (λ () (parse true)))
(check-exn #px"ZNQR: duplicate function arguments"
           (λ ()
            (parse '{{{z z} -> {+ z z}} {+ 9 14} 98})))
(check-exn #px"ZNQR: duplicate function arguments"
           (λ ()
            (parse '{var {z = {+ 9 14}} {z = 98} {+ z z}})))
(check-exn #px"ZNQR: invalid variable name"
           (λ ()
             (parse '(var (-> = "") "World"))))
(check-exn #px"ZNQR: invalid variable name"
           (λ ()
             (parse '(var (if = "") "World"))))
(check-exn #px"ZNQR: invalid variable name"
           (λ ()
             (parse '(var (= = "") "World"))))
(check-exn #px"ZNQR: invalid variable name"
           (λ ()
             (parse '(var (var = "") "World"))))

; testing return-ids
(check-equal? (return-ids '{{z = {+ 9 14}} {y = 98}})
              (list 'z 'y))

; testing return-exprs
(check-equal? (return-exprs '{{z = {+ 9 14}} {y = 98}})
              (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                    (NumC 98)))
