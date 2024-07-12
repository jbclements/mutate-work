#lang typed/racket

;;> eyeball: 6/6, Very nice, see comment below

(require typed/rackunit)

;Expr = Num
;| id
;| String
;| {if Expr Expr Expr}
;| {var {id = Expr} ... Expr}
;| {lam {id ...} Expr}
;| {Expr Expr ...}

;; I completed all parts of this assigment

;Data Structures----------------------------------------------------------------
(define-type-alias  Env (Listof Bind))
(struct Bind ([name : Symbol] [val : Value])#:transparent)
(define mt-env empty)
(define extend-env append)

(define-type ExprC (U numC stringC idC appC ifC lamC))
  (struct stringC ([s : String])#:transparent)
  (struct ifC ([test : ExprC] [then : ExprC] [el : ExprC])#:transparent)
  (struct idC ([s : Symbol])#:transparent)
  (struct appC ([fun : ExprC] [args : (Listof ExprC)])#:transparent)
  (struct lamC ([param : (Listof Symbol)] [body : ExprC])#:transparent)
  (struct numC ([n : Real])#:transparent)

(define-type Value (U numV stringV boolV primV closV))
  (struct numV ([n : Real])#:transparent)
  (struct stringV ([s : String])#:transparent)
  (struct boolV ([b : Boolean])#:transparent)
  (struct primV ([p : (Value Value -> Value)])#:transparent)
  (struct closV ([param : (Listof Symbol)] [body : ExprC] [env : Env])#:transparent)

(define Top-env (list (Bind '+ (primV (lambda ([a : Value] [b : Value])
                                        (numV (+ (check-num a) (check-num b))))))
                      (Bind '* (primV (lambda ([a : Value] [b : Value])
                                        (numV (* (check-num a) (check-num b))))))
                      (Bind '- (primV (lambda ([a : Value] [b : Value])
                                        (numV (- (check-num a) (check-num b))))))
                      (Bind '/ (primV (lambda ([a : Value] [b : Value])
                                        (numV (/ (check-num a) (check-zero(check-num b)))))))
                      (Bind '<= (primV  (lambda ([a : Value] [b : Value])
                                          (boolV (<= (check-num a) (check-num b))))))
                      (Bind 'equal? (primV  (lambda ([a : Value]
                                                     [b : Value]) (myequal? a b))))
                      (Bind 'true (boolV #t))
                      (Bind 'false (boolV #f))))

;Helper function that checks two values and returns a boolV
(define (myequal? [a : Value] [b : Value])
  : Value
  (cond
    [(or (primV? a) (primV? b)) (boolV #f)]
    [(or (closV? a) (closV? b)) (boolV #f)]
    [else (cond
            [(and (stringV? a) (stringV? b))
             (boolV (equal? (stringV-s a) (stringV-s b)))]
            [(and (boolV? a) (boolV? b))
             (boolV (equal? (boolV-b a) (boolV-b b)))]
            [(and (numV? a) (numV? b))
             (boolV (equal? (numV-n a) (numV-n b)))]
            [else (boolV #f)])]))

;Helper function that checks a Value
(define (check-num [val : Value])
  : Real
  (cond
    [(numV? val)
     (numV-n val)]
    [else (error 'Prim "ZNQR: Expected a Real value: ~e" val)]))

;Helper function that checks if a value is zero
(define (check-zero [val : Real])
  : Real
  (cond
    [(equal? val 0) (error 'check-zero "ZNQR: Division by 0: ~e" val)]
    [else val]))

;Interp-------------------------------------------------------------------------
;Accepts an expression an produces its value
(define (interp [exp : ExprC] [env : Env])
  : Value
  (match exp
      [(numC n) (numV n)]
      [(stringC s) (stringV s)]
      [(idC s) (Lookup s env)]
      [(appC f args) (match (interp f env)
                       [(primV op) (define vals (get-vals args env))
                                   (cond
                                    [(equal? (length vals) 2)
                                     (op (first vals) (second vals))]
                                    [else
                                     (error
                                      'interp
                                      "ZNQR: Expected 2 arguments: ~e"
                                      (length vals))])]
                       [(closV param body clo-env)
                          (interp body
                                  (extend-env
                                   (bind-all param
                                             (get-vals args env))
                                   clo-env))]
                       [else (error 'interp "ZNQR: Application of a non-closure: ~e" f)])]
      [(lamC a b) (closV a b env)]
      [(ifC t th el) (define test (interp t env))
                     (match test
                       [(boolV b) (if b (interp th env) (interp el env))]
                       [else (error 'interp "ZNQR: Expected a Boolean test")])]))

;creates a list of bindings and values for the given variables and thier corresponding values
(define (bind-all [var : (Listof Symbol)] [vals : (Listof Value)])
  : (Listof Bind)
  (cond
    [(equal? (equal? (length vals) (length var)) #f)
     (error 'bind-all "ZNQR: wrong arity: ~e" vals)]
    [(empty? var) empty]
    [else (cons (Bind (first var) (first vals)) (bind-all (rest var) (rest vals)))]))

;Look up - takes a symbol and looks it up in the enviorment
(define (Lookup [for : Symbol] [env : Env])
  : Value
  (cond
    [(empty? env) (error 'Lookup "ZNQR: Symbol not found: ~e" for)]
    [else (cond
            [(symbol=? for (Bind-name (first env)))
             (Bind-val (first env))]
            [else (Lookup for (rest env))])]))

;;> can also use map to do this
;Helper function that generates a list of (values)
(define (get-vals [args : (Listof ExprC)] [env : Env])
 : (Listof Value)
  (cond
    [(empty? args) empty]
    [else (cons (interp (first args) env) (get-vals(rest args) env))]))

;Parse--------------------------------------------------------------------------
;parse function and map Sexp to ExprC
(define (parse [exp : Sexp])
  : ExprC
  (match exp
    [(? real?) (numC exp)]
    [(? string?) (stringC exp)]
    [(? symbol?) (cond
                     [(or (eq? exp 'if) (eq? exp 'var))
                      (error 'parse "ZNQR: Invalid input: ~e" exp)]
                     [(or (eq? exp '->) (eq? exp '=))
                      (error 'parse "ZNQR: Invalid input: ~e" exp)]
                     [else (idC exp)])]
    [(list (? symbol? 'if) t th el) (ifC (parse t) (parse th) (parse el))]
    [(list a (? symbol? '->) b) (match a
                                   [(list args ...) (lamC (check-args args) (parse b))])]
    [(list 'var a ... b) (cond
                         [(check-dup (map get-params a))
                          (error 'parse "ZNQR: Cannot have duplicate parameters")]
                         [else (appC (lamC (map get-params a) (parse b))
                                     (map parse (map get-args a)))])]
    [(list a b ...) (appC (parse a) (map parse b))]
    [else (error 'parse "ZNQR: Invalid input: ~e" exp)]))

;Helper Function that gets a parameter from an expresion
(define (get-params [exp : Any])
  : Symbol
  (match exp
    [(list (? symbol? s) '= a) (cond
                                 [(or (eq? s 'if) (eq? s 'var))
                      (error 'parse "ZNQR: Invalid input: ~e" exp)]
                     [(or (eq? s '->) (eq? s '=))
                      (error 'parse "ZNQR: Invalid input: ~e" exp)]
                     [else s])]
    [else (error 'parse "ZNQR: Invalid input: ~e" exp)]))

;Helper Function that gets the args from an expresion
(define (get-args [exp : Any])
  : Sexp
  (match exp
    [(list s '= a) (cast a Sexp)]))

;Helper Function that returns a list of symbols or results and an error if not a symbol
(define (check-args [args : (Listof Any)])
  : (Listof Symbol)
  (cond
    [(empty? args) '()]
    [(check-dup args)
     (error 'check-args "ZNQR: Cannot have duplicate parameters: ~e" args)]
    [(symbol? (first args)) (cons (first args) (check-args (rest args)))]
    [else (error 'check-args "ZNQR: Invalid input: ~e" args)]))

;Helper Function that Checks for duplicates
(define (check-dup [args : (Listof Any)])
  : Boolean
  (cond
    [(eq? (check-duplicates args) #f) #f]
    [else #t]))

;Top-Interp---------------------------------------------------------------------
;accepts an Sexp and calls the parser, desugar and interp functions
(define (top-interp [exp : Sexp])
  (serialize (interp (parse exp) Top-env)))

;Serialize----------------------------------------------------------------------
;Accepts a Value and returns a String representation
(define (serialize [val : Value])
  : String
  (match val
    [(numV n) (~v n)]
    [(stringV s) (~v s)]
    [(boolV b) (cond
                 [(equal? b #t) "true"]
                 [else "false"])]
    [(closV param body env) "#<procedure>"]
    [(primV p) "#<primop>"]))

;Test Cases---------------------------------------------------------------------
;Test for Top-interp------------------------------------------------------------
(define test1 '{{{z y} -> {+ z y}} {+ 9 14} 98})
(define test1.2 '{{{{z} -> {{y} -> {+ y z}}} 3}3})
(define test1.3 '{{{{z} -> {{y} -> {* y z}}} 3}3})
(define test1.4 '{{{{z} -> {{y} -> {+ {/ y z} z}}} 3}3})
(define test2 '{{{z y} -> {- z y}} 1 23})
(define test3 '{{{z y} -> {* z y}} 5 6})
(define test4 '{{{z y} -> {<= z y}} 5 6})
(define test5 '{{{z y} -> {<= z y}} 7 6})
(define test6 '{{a b c} -> 3})
(define test7 '{{{a b c} -> 3} 1 2 3})
(define test8 '{{{a b c} -> " 1 2 3"} 1 2 3})
(define test9 '{{{f g} -> {f {g 3}}}
                       {{x} -> {/ x 3}}
                       {{x} -> {* x 2}}})
(define test10 '{{{f g} -> {f {g 3}}}
                       {{x} -> {/ x 0}}
                       {{x} -> {* x 2}}})
(define test10.2 '{{{x z} -> {+ {x 2} {z 9}}}
                       {{x} -> {+ x 1}}
                       {{-} -> {+ - 2}}})
(define test10.3 '{{{x z} -> {+ {x 2} {z 9}}}
                       {{+} -> {+ + 1}}
                       {{-} -> {+ - 2}}})
(define test10.4 '{{{f g} -> {if {<= {f 2} {g 1}}
                                 {+ {f{g 1}} {g {f 2}}}
                                 {- {g {f 2}} {f {g 1}}}}}
                       {{x} -> {+ x 1}}
                       {{z} -> {+ z 2}}})
(define test24 '{var {z = {+ 9 14}}
                     {y = 98}
                     {+ z y}})
(define test25 '{var {z = {+ 9 14}}
                     {y = 98}
                     {+ z y x}})
(define test26 '{var {z = {+ 5 3}}
                     {y = 8}
                     {x = true}
                     {f = false}
                     {if {<= z y} x f}})
(define test27 '{var {f = {{x} -> {+ x 1}}}
                     {g = {{z} -> {+ z 2}}}
                     {+ {f 2} {g 9}}})
(define test28 '{{{} -> 9} 7})
(define test11 '{{{z y} -> {equal? z y}} {+ 9 14} 98})
(define test12 '{{{z y} -> {equal? z y}} {+ 9 14} {{a b c} -> 3}})
(define test13 '{{{z y} -> {equal? z y}} + {{a b c} -> 3}})
(define test14 '{{{z y} -> {equal? z y}} {+ 2 1} 3})
(define test15 '{{{z y} -> {equal? z y}} "test" 3})
(define test16 '{{{z y} -> {equal? z y}} true false})
(define test17 '{{{z y} -> {equal? z y}} "test" "test2"})
(define test18 '{{{z y} -> {equal? z y}} true true})
(define test19 '{{{z y} -> {equal? z y}} "test" "test"})
(define test20 '{{{z 1} -> {equal? z 1}} "test" "test"})
(define test21 '{{{z y} -> {equal? z y}} "test"})
(define test22 '{{{z y} -> {equal? z}} "test" "test"})
(define test23 '{{{x y z} -> {+ x y z}} 1 2 3})
(check-equal? (top-interp test1) "121")
(check-equal? (top-interp test1.2) "6")
(check-equal? (top-interp test1.3) "9")
(check-equal? (top-interp test1.4) "4")
(check-equal? (top-interp test2) "-22")
(check-equal? (top-interp test3) "30")
(check-equal? (top-interp test4) "true")
(check-equal? (top-interp test5) "false")
(check-equal? (top-interp test6) "#<procedure>")
(check-equal? (top-interp test7) "3")
(check-equal? (top-interp test8) "\" 1 2 3\"")
(check-equal? (top-interp test9) "2")
(check-equal? (top-interp test10.2) "14")
(check-equal? (top-interp test10.4) "9")
(check-equal? (top-interp test11) "false")
(check-equal? (top-interp test12) "false")
(check-equal? (top-interp test13) "false")
(check-equal? (top-interp test14) "true")
(check-equal? (top-interp test15) "false")
(check-equal? (top-interp test16) "false")
(check-equal? (top-interp test17) "false")
(check-equal? (top-interp test18) "true")
(check-equal? (top-interp test19) "true")
(check-equal? (top-interp test24) "121")
(check-equal? (top-interp test26) "true")
(check-equal? (top-interp test27) "14")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '-) "#<primop>")
(check-equal? (top-interp '*) "#<primop>")
(check-equal? (top-interp '/) "#<primop>")
(check-equal? (top-interp '<=) "#<primop>")
(check-exn (regexp (regexp-quote  "ZNQR: Division by 0"))
           (lambda () (top-interp test10)))
(check-exn (regexp (regexp-quote  "ZNQR: Application of a non-closure"))
           (lambda () (top-interp test10.3)))
(check-exn (regexp (regexp-quote  "ZNQR: Invalid input"))
           (lambda () (top-interp test20)))
(check-exn (regexp (regexp-quote  "ZNQR: wrong arity"))
           (lambda () (top-interp test21)))
(check-exn (regexp (regexp-quote  "ZNQR: Expected 2 arguments"))
           (lambda () (top-interp test22)))
(check-exn (regexp (regexp-quote  "ZNQR: Expected 2 arguments"))
           (lambda () (top-interp test23)))
(check-exn (regexp (regexp-quote  "ZNQR: Symbol not found"))
           (lambda () (top-interp test25)))
(check-exn (regexp (regexp-quote  "ZNQR: wrong arity"))
           (lambda () (top-interp test28)))
;Test for Interp----------------------------------------------------------------
(check-equal? (interp (parse '{+ 2 2}) Top-env) (numV 4))
(check-equal? (interp (parse '{/ 2 2}) Top-env) (numV 1))
(check-equal?  (interp  (parse '{+ {* 1 2} {+ 2 3}}) Top-env) (numV 7))
(check-equal? (interp (parse'{+{- 2 3}3}) Top-env) (numV 2))
(check-equal? (interp (parse '{if {<= 2 1} 1 {- 3 1}}) Top-env) (numV 2))
(check-equal? (interp (parse '{if {equal? true true} 1 2}) Top-env) (numV 1))
(check-exn (regexp (regexp-quote  "ZNQR: Division by 0"))
           (lambda () (interp (parse '{/ 2 0}) Top-env)))
(check-exn (regexp (regexp-quote  "ZNQR: Symbol not found"))
           (lambda () (interp (idC 'x) Top-env)))
(check-exn (regexp (regexp-quote  "ZNQR: Expected a Real value"))
           (lambda () (interp (parse '{+ 1 true}) Top-env)))
(check-exn (regexp (regexp-quote  "ZNQR: Expected a Real value"))
           (lambda () (interp (parse '{+ false 1}) Top-env)))
(check-exn (regexp (regexp-quote  "ZNQR: Expected a Boolean test"))
           (lambda () (interp (parse'{if {- 1 1} 1 {- 3 1}}) Top-env)))
;Tests for parse----------------------------------------------------------------
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{if + 3 4 5})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{if + +})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{var})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{->})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{=})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{if})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse 'if)))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{if x y z f})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{var {-> = ""} "world"})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{var {if = ""} "world"})))
(check-exn (regexp (regexp-quote "Cannot have duplicate parameters"))
           (lambda () (parse '{{z z} -> {+ z z}})))
(check-exn (regexp (regexp-quote "Cannot have duplicate parameters"))
           (lambda () (parse '{var {z = {+ 9 14}}
                                   {z = 98}
                                   {+ z y}})))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse '{var {z  x {+ 9 14}}
                                   {z y 98}
                                   {+ z y}})))
(check-equal? (parse "junk") (stringC "junk"))
(check-equal? (parse '{{a b c} -> 3}) (lamC '(a b c) (numC 3)))
(check-equal? (parse '{{z} -> {{y} -> {+ z y}}})
             (lamC '(z) (lamC '(y) (appC (idC '+) (list (idC 'z) (idC 'y))))))
(check-equal? (parse  '{{{z y} -> {+ z y}} 1 23})
             (appC
              (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
              (list (numC 1) (numC 23))))
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98}{+ z y}})
(appC (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
      (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
;Test for Serialize-------------------------------------------------------------
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize (stringV "test")) "\"test\"")
(check-equal? (serialize (numV 4)) "4")
(check-equal? (serialize (closV (list 'x) (idC 'x) mt-env)) "#<procedure>")
(check-equal? (serialize (interp(parse '{{a} -> 3}) Top-env)) "#<procedure>")
