#lang typed/racket

;;> eyeball: 6/6, Very nice code

(require typed/rackunit)

; Assignment complete.

; A ZNQR value is one of:
; - a real number, or
; - a boolean, or
; - a string, or
; - a closure, or
; - a primitive operator.
(define-type Value (U NumV BoolV StringV ClosV PrimopV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([bool : Boolean]) #:transparent)
(struct StringV ([str : String]) #:transparent)
(struct ClosV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimopV ([sym : Symbol]) #:transparent)

; A ZNQR expression is one of:
; - a value, or
; - an if-less-than-or-equal-to-zero testing expression, or
; - a variable identifier, or
; - a function (lambda), or
; - a function application.
(define-type ExprC (U Value IfC VarC FunC AppC))
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct VarC ([sym : Symbol]) #:transparent)
(struct FunC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)

; A binding maps a symbol name to a value.
(struct Binding ([name : Symbol] [value : Value]) #:transparent)

; An environment is a list of bindings.
(define-type-alias Env (Listof Binding))

; Describes an empty environment.
(: empty-env Env)
(define empty-env empty)

; Extends the environment with an additional binding.
(: extend-env (-> Binding Env Env))
(define extend-env cons)

; Lifts a binary numeric operator on reals into an operator on Value instances.
(: lift-binop (-> (-> Real Real Real) (-> (Listof Value) Value)))
(define (lift-binop op)
  (λ (args)
    (match args
      [(list (NumV first) (NumV second)) (NumV (op first second))]
      [else (error 'ZNQR "Numeric operator expects two numeric operands")])))

; Describes a mapping from primitive operator symbols to their function implementations.
(: primops (Immutable-HashTable Symbol (-> (Listof Value) Value)))
(define primops (hash
                 '+ (lift-binop +)
                 '- (lift-binop -)
                 '* (lift-binop *)
                 '/ (λ (args)
                      (match args
                        [(list (NumV n) (NumV d))
                         (if (zero? d) (error 'ZNQR "Division by zero") (NumV (/ n d)))]
                        [else (error 'ZNQR "Numeric operator expects two numeric operands")]))
                 '<= (λ (args)
                       (match args
                         [(list (NumV a) (NumV b)) (BoolV (<= a b))]
                         [else (error 'ZNQR "Numeric operator expects two numeric operands")]))
                 'equal? (λ (args)
                             (match args
                               [(list (NumV a) (NumV b)) (BoolV (equal? a b))]
                               [(list (BoolV a) (BoolV b)) (BoolV (equal? a b))]
                               [(list (StringV a) (StringV b)) (BoolV (equal? a b))]
                               [(list _ _) (BoolV false)]
                               [else (error `ZNQR "equal? operator expects two operands")]))))

; Determines whether a symbol is a reserved word.
(: reserved (-> Symbol Boolean))
(define (reserved sym)
  (match sym
    [(or 'if 'var '-> '=) true]
    [else false]))

; Interprets a ZNQR program.
(: top-interp (-> Sexp String))
(define (top-interp s)
  (serialize (interp (parse s) top-env)))

; Transforms a ZNQR value into a string.
(: serialize (-> Value String))
(define (serialize v)
  (match v
    [(NumV n) (~v n)]
    [(BoolV b) (if b "true" "false")]
    [(StringV s) (~v s)]
    [(? ClosV? _) "#<procedure>"]
    [(? PrimopV? _) "#<primop>"]))

; The boolean primitive bindings.
(define bools (list (Binding 'true (BoolV true))
                    (Binding 'false (BoolV false))))

; The primitive operator bindings.
(define prims (map (λ ([sym : Symbol]) (Binding sym (PrimopV sym)))
                   (hash-keys primops)))

; The top-level environment containing ZNQR primitives.
(: top-env Env)
(define top-env (append bools prims))

; Evaluates a ZNQR expression.
(: interp (-> ExprC Env Value))
(define (interp exp env)
  (match exp
    [(? NumV? v) v]
    [(? BoolV? v) v]
    [(? StringV? v) v]
    [(? PrimopV? v) v]
    [(IfC test then else)
     (match (interp test env)
       [(BoolV bool) (if bool (interp then env) (interp else env))]
       [else (error `ZNQR "Expected boolean in `if` test")])]
    [(VarC sym) (lookup sym env)]
    [(FunC args body) (ClosV args body env)]
    [(AppC fun args)
     (define evaluated-args (map (λ ([arg : ExprC]) (interp arg env)) args))
     (match (interp fun env)
       [(PrimopV sym)
        (define op (hash-ref primops sym))
        (op evaluated-args)]
       [(ClosV params body clos-env)
        (cond [(equal? (length args) (length params))
               (define new-bindings (map Binding params evaluated-args))
               (interp body (append new-bindings clos-env))]
              [else (error `ZNQR "Expected ~e arguments but received ~e"
                           (length params) (length args))])]
       [else (error `ZNQR "Expected function to apply")])]))

; Returns the value of symbol in the environment.
(: lookup (-> Symbol Env Value))
(define (lookup sym env)
  (define found (findf (λ ([b : Binding]) (symbol=? (Binding-name b) sym)) env))
  (match found
    [(Binding _ value) value]
    [else (error `ZNQR "Unbound identifier ~e" sym)]))

; Parses an ExprC from concrete ZNQR syntax.
(: parse (-> Sexp ExprC))
(define (parse exp)
  (match exp
    [(? real? num) (NumV num)]
    ['true (BoolV true)]
    ['false (BoolV false)]
    [(? string? str) (StringV str)]
    [(? symbol? sym) #:when (false? (reserved sym)) (VarC sym)]
    [(list 'if test then else) (IfC (parse test) (parse then) (parse else))]
    [(list 'var (list (? symbol? syms) '= exprs) ... body)
     (define var-syms (cast syms (Listof Symbol)))
     (cond [(check-duplicates var-syms) (error `ZNQR "var binds identifier to multiple values")]
           [(findf reserved var-syms) (error `ZNQR "var uses reserved identifier")]
           [else (define var-asgns (map parse (cast exprs (Listof Sexp))))
                 (AppC (FunC var-syms (parse body)) var-asgns)])]
    [(list (list (? symbol? params) ...) '-> body)
     (define param-syms (cast params (Listof Symbol)))
     (cond [(check-duplicates param-syms) (error `ZNQR "Function has parameters with same identifiers")]
           [else (FunC param-syms (parse body))])]
    [(list fun args ...) (AppC (parse fun) (map parse args))]
    [else (error `ZNQR "Unable to parse ~e" exp)]))

; Tests
; top-interp tests
(check-equal? (top-interp '3)
              "3")
(check-equal? (top-interp 'false)
              "false")
(check-equal? (top-interp '{if true "yep!" false})
              "\"yep!\"")
(check-equal? (top-interp '{var {square = {{n} -> {* n n}}}
                                {x = 3}
                                {square x}})
              "9")
(check-equal? (top-interp '{var {twice = {{f} -> {{x} -> {f {f x}}}}}
                                {double = {{y} -> {* 2 y}}}
                                {{twice double} 5}})
              "20")
(check-equal? (top-interp '{var {compose = {{f g} -> {{x} -> {g {f x}}}}}
                                {incr = {{x} -> {+ 1 x}}}
                                {even = {{x} -> {equal? x {* {/ x 2} 2}}}}
                                {var {odd = {compose incr even}}
                                     {odd 5}}})
              "true")
(check-equal? (top-interp '{var {not = {{p} -> {if p false true}}}
                                {var {negate = {{pred} -> {{p} -> {not {pred p}}}}}
                                     {<=0? = {{x} -> {<= x 0}}}
                                     {var {positive? = {negate <=0?}}
                                          {positive? {+ 1 1}}}}})
              "true")
(check-equal? (top-interp '{if false {+ 1 "not an number"} 2})
              "2")
(check-equal? (top-interp '{equal? "one" "two"})
              "false")
(check-equal? (top-interp '{{{+} -> {* + +}} 12})
              "144")
(check-equal? (top-interp '{var {+ = -} {- = +} {* {+ 3 1} {- 2 2}}})
              "8")
(check-exn #px"ZNQR: equal\\? operator expects two operands"
           (λ () (top-interp '{equal? 1 2 3})))
(check-exn #px"ZNQR: Numeric operator expects two numeric operands"
           (λ () (top-interp '{if true {+ 1 "not an number"} 2})))

; serialize tests
(check-equal? (serialize (NumV 3))
              "3")
(check-equal? (serialize (BoolV true))
              "true")
(check-equal? (serialize (BoolV false))
              "false")
(check-equal? (serialize (StringV "hi"))
              "\"hi\"")
(check-equal? (serialize (ClosV '() (NumV 1) empty-env))
              "#<procedure>")
(check-equal? (serialize (PrimopV '+))
              "#<primop>")

; interp tests
(check-equal? (interp (NumV 5) empty-env)
              (NumV 5))
(check-equal? (interp (StringV "") empty-env)
              (StringV ""))
(check-equal? (interp (AppC (PrimopV '+) (list (NumV 1) (NumV 2))) empty-env)
              (NumV 3))
(check-equal? (interp (AppC (PrimopV '/) (list (NumV 4) (AppC (PrimopV '-) (list (NumV 5) (NumV 3))))) empty-env)
              (NumV 2))
(check-equal? (interp (AppC (PrimopV '*) (list (NumV 2) (AppC (PrimopV '+) (list (NumV 0) (NumV -1))))) empty-env)
              (NumV -2))
(check-equal? (interp (AppC (PrimopV '<=) (list (NumV 3) (NumV 2))) empty-env)
              (BoolV false))
(check-equal? (interp (AppC (PrimopV 'equal?) (list (NumV 2) (NumV 2))) empty-env)
              (BoolV true))
(check-equal? (interp (AppC (PrimopV 'equal?) (list (BoolV true) (BoolV true))) empty-env)
              (BoolV true))
(check-equal? (interp (AppC (PrimopV 'equal?) (list (PrimopV '+) (BoolV true))) empty-env)
              (BoolV false))
(check-equal? (interp (IfC (BoolV true) (NumV 1) (NumV 2)) empty-env)
              (NumV 1))
(check-equal? (interp (IfC (BoolV false) (NumV 1) (AppC (PrimopV '+) (list (NumV 2) (NumV 3)))) empty-env)
              (NumV 5))
(check-equal? (interp (AppC (FunC (list 'x 'y) (AppC (PrimopV '+) (list (VarC 'x) (VarC 'y))))
                            (list (NumV 1) (NumV 2))) empty-env)
              (NumV 3))
(check-equal? (interp (AppC (VarC 'f) (list (NumV 1) (NumV 2)))
                      (list (Binding 'f (ClosV (list 'a 'b) (AppC (PrimopV '*) (list (VarC 'a) (VarC 'b))) empty-env))))
              (NumV 2))
(check-exn #px"ZNQR: Expected boolean in `if` test"
           (λ () (interp (IfC (NumV 1) (NumV 2) (NumV 3)) empty-env)))
(check-exn #px"ZNQR: Unbound identifier"
           (λ () (interp (VarC 'x) empty-env)))
(check-exn #px"ZNQR: Expected function to apply"
           (λ () (interp (AppC (NumV 1) (list (NumV 2))) empty-env)))
(check-exn #px"ZNQR: Expected 2 arguments but received 1"
           (λ () (interp (AppC (FunC (list 'a 'b) (NumV 1)) (list (NumV 1))) empty-env)))
(check-exn #px"ZNQR: Numeric operator expects two numeric operands"
           (λ () (interp (AppC (PrimopV '+) '()) empty-env)))
(check-exn #px"ZNQR: Numeric operator expects two numeric operands"
           (λ () (interp (AppC (PrimopV '/) '()) empty-env)))
(check-exn #px"ZNQR: Numeric operator expects two numeric operands"
           (λ () (interp (AppC (PrimopV '<=) '()) empty-env)))
(check-exn #px"ZNQR: Division by zero"
           (λ () (interp (AppC (PrimopV '/) (list (NumV 1) (AppC (PrimopV '+) (list (NumV 1) (NumV -1))))) empty-env)))

; lookup tests
(check-equal? (lookup 'x (list (Binding 'y (NumV 2)) (Binding 'x (NumV 1)))) (NumV 1))
(check-exn #px"ZNQR: Unbound identifier"
           (λ () (lookup 'x '())))
(check-exn #px"ZNQR: Unbound identifier"
           (λ () (lookup 'x (list (Binding 'y (NumV 1)) (Binding 'z (NumV 2))))))

; parse tests
(check-equal? (parse '3)
              (NumV 3))
(check-equal? (parse "i'm a string")
              (StringV "i'm a string"))
(check-equal? (parse '{+ 1 2})
              (AppC (VarC '+) (list (NumV 1) (NumV 2))))
(check-equal? (parse '{* 3 {+ 4 5}})
              (AppC (VarC '*) (list (NumV 3) (AppC (VarC '+) (list (NumV 4) (NumV 5))))))
(check-equal? (parse '{- 100 99})
              (AppC (VarC '-) (list (NumV 100) (NumV 99))))
(check-equal? (parse '{/ 4 {+ 1 1}})
              (AppC (VarC '/) (list (NumV 4) (AppC (VarC '+) (list (NumV 1) (NumV 1))))))
(check-equal? (parse '{if true 1 2})
              (IfC (BoolV true) (NumV 1) (NumV 2)))
(check-equal? (parse '{if false 1 {* 2 2}})
              (IfC (BoolV false) (NumV 1) (AppC (VarC '*) (list (NumV 2) (NumV 2)))))
(check-equal? (parse 'x)
              (VarC 'x))
(check-equal? (parse '{{} -> 1})
              (FunC '() (NumV 1)))
(check-equal? (parse '{{x} -> x})
              (FunC (list 'x) (VarC 'x)))
(check-equal? (parse '{{{x} -> x} 1})
              (AppC (FunC (list 'x) (VarC 'x)) (list (NumV 1))))
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}})
              (AppC (FunC (list 'z 'y) (AppC (VarC '+) (list (VarC 'z) (VarC 'y))))
                    (list (AppC (VarC '+) (list (NumV 9) (NumV 14))) (NumV 98))))
(check-exn #px"ZNQR: Function has parameters with same identifiers"
           (λ () (parse '{{x x} -> x})))
(check-exn #px"ZNQR: Unable to parse"
           (λ () (parse 'if)))
(check-exn #px"ZNQR: Unable to parse"
           (λ () (parse '{var {3 = 5} {3}})))
(check-exn #px"ZNQR: Unable to parse"
           (λ () (parse '{var {1 2} {3}})))
(check-exn #px"ZNQR: var binds identifier to multiple values"
           (λ () (parse '{var {x = 1} {x = 2} {x}})))
(check-exn #px"ZNQR: var uses reserved identifier"
           (λ () (parse '{var {if = 1} {if}})))

; lift-binop tests
(check-equal? ((lift-binop +) (list (NumV 1) (NumV 2))) (NumV 3))
(check-equal? ((lift-binop *) (list (NumV 4) (NumV 8))) (NumV 32))
(check-exn #px"ZNQR: Numeric operator expects two numeric operands"
           (λ () ((lift-binop +) '())))
