#lang typed/racket

;;> eyeball: 6/6, Looks good, see comment below

(require typed/rackunit)

; COMPLETION: Full project implemented.

; TYPES AND DATA STRUCTURES SECTION

; Types representing ZNQR2 expressions
(define-type ExprC (U NumC IfThenElseC AppC IdC LamC StringC))
(struct NumC ([n : Real]) #:transparent)
(struct IfThenElseC ([test : ExprC] [then : ExprC] [else-result : ExprC]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct StringC ([str : String]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)

; Env is listof bindings, mt-env is empty environment, and use cons to extend environment
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof Binding))
(define mt-env '())
(define extend-env cons)

; Type definitions necessary for higher order functions
(define-type Value (U NumV ClosV PrimV BoolV StringV))
(struct NumV ([n : Real]) #:transparent)
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([op : Symbol]) #:transparent)
(struct BoolV ([bool : Boolean]) #:transparent)
(struct StringV ([s : String]) #:transparent)

; Top-level environment
(define top-env (list (Binding '+ (PrimV '+))
                      (Binding '- (PrimV '-))
                      (Binding '/ (PrimV '/))
                      (Binding '* (PrimV '*))
                      (Binding '<= (PrimV '<=))
                      (Binding 'equal? (PrimV 'equal?))
                      (Binding 'true (BoolV #t))
                      (Binding 'false (BoolV #f))))


; TOP-INTERP SECTION

; top-interp parses an Sexp (representing the program) and then interprets it, returning a String representation
; of the resulting value.
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; INTERP SECTION

; interp function takes in an ExprC and an environment and evaluates the expression, returning a value.
(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(IdC id) (lookup id env)]
    [(LamC a b) (ClosV a b env)]
    [(AppC f a)
     (match (interp f env)
       [(ClosV args body clos-env)
        (cond
          [(= (length args) (length a))
           (interp body
                   (append (map (lambda ([arg : Symbol] [argval : ExprC])
                                  (Binding arg (interp argval env)))
                                args a) clos-env))]
          [else (error 'interp "ZNQR: not valid argument list length")])]
       [(PrimV op) (prim-helper op (map (lambda ([argval : ExprC])
                                          (interp argval env)) a))]
       [_ (error 'interp "ZNQR: Invalid value for AppC")])]
    [(IfThenElseC test then else-result) (if-then-else-helper test then else-result env)]))


; REST OF CODE SECTION

; Serialize function takes a value and returns the string representation of that value.
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (~v n)]
    [(BoolV #t) "true"]
    [(BoolV #f) "false"]
    [(StringV s) (~v s)]
    [(PrimV op) "#<primop>"]
    [(ClosV a b env) "#<procedure>"]))

; Parse function takes in an Sexp and converts it into an ExprC.
; Additionally, it makes sure that the Sexps parsed adhere to ZNQR syntax.
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? num) (NumC num)]
    [(? string? str) (StringC str)]
    [(? symbol? id) (cond
                      [(is-id? id) (IdC id)]
                      [else (error 'parse "ZNQR: Parse error")])]
    [(list 'if a b c) (IfThenElseC (parse a) (parse b) (parse c))]
    [(list 'var (list (? symbol? id) '= id-expr) ... expr)
     (cond
       [(check-dup-params (cast id (Listof Symbol))) (error 'parse "ZNQR: Duplicate names error")]
       [(not (andmap is-id? (cast id (Listof Symbol)))) (error 'parse "ZNQR: Invalid ID error")]
       [else (AppC (LamC (cast id (Listof Symbol)) (parse expr)) (map parse (cast id-expr (Listof Sexp))))])]
    [(list (list (? symbol? #{ids : (Listof Symbol)}) ...) '-> expr)
     (cond
       [(check-dup-params ids) (error 'parse "ZNQR: Duplicate names error")]
       [(not (andmap is-id? ids)) (error 'parse "ZNQR: Invalid ID error")]
       [else (LamC ids (parse expr))])]
    [(list expr expr-args ...) (AppC (parse expr) (map parse expr-args))]
    [_ (error 'parse "ZNQR: Parse error")]))


; is-id? helper function that determines whether a given symbol is an ID or not.
; (An ID is a symbol that is not 'var, 'if, '->, or '=
(define (is-id? [s : Symbol]) : Boolean
  (not (or (symbol=? s 'var) (symbol=? s 'if) (symbol=? s '->) (symbol=? s '=))))

; if-then-else-helper handles the conditional case for evaluation.
; returns the evaluation of then if the test value is (a boolean and) true, else otherwise.
(define (if-then-else-helper [test : ExprC] [then : ExprC] [else-result : ExprC] [env : Env]) : Value
  (define test-val (interp test env))
  (cond
    [(BoolV? test-val)
     (cond
       [(BoolV-bool test-val) (interp then env)]
       [else (interp else-result env)])]
    [else (error 'if-then-else-helper "ZNQR: Test value is not a boolean.")]))

; helper function for PrimV case for AppC case of interp
(define (prim-helper [op : Symbol] [arg-vals : (Listof Value)]) : Value
  (match arg-vals
    [(list (? NumV? a) (? NumV? b))
     (cond
       [(symbol=? op '/) (cond
                           [(= (NumV-n b) 0) (error 'prim-helper "ZNQR: Div by 0")]
                           [else (NumV (/ (NumV-n a) (NumV-n b)))])]
       [(symbol=? op '*) (NumV (* (NumV-n a) (NumV-n b)))]
       [(symbol=? op '+) (NumV (+ (NumV-n a) (NumV-n b)))]
       [(symbol=? op '-) (NumV (- (NumV-n a) (NumV-n b)))]
       [(symbol=? op '<=) (BoolV (<= (NumV-n a) (NumV-n b)))]
       [(symbol=? op 'equal?) (BoolV (equal? a b))]
       [else (error 'prim-helper "ZNQR: Invalid primitive operator")])]
    [(list a b) (cond
                  [(and (symbol=? op 'equal?) (not (or (PrimV? a) (PrimV? b) (ClosV? a) (ClosV? b))))
                   (BoolV (equal? a b))]
                  [(symbol=? op 'equal?) (BoolV #f)]
                  [else (error 'prim-helper "ZNQR: Invalid argument for primitive operator")])]
    [_ (error 'prim-helper "ZNQR: Invalid argument for primitive operator")]))

; check-dup-params takes a list of symbols and detects whether the list has duplicate param names.
; Used to check for duplicate IDs in lambda expressions/variable assignments.
(define (check-dup-params [params : (Listof Symbol)]) : Boolean
  (cond
    [(empty? params) #f]
    [(contains? (rest params) (first params)) #t]
    [else (check-dup-params (rest params))]))

;;> there is a built in function in racket for this and also one that checks for duplicates
; contains? is a helper function that consumes a list and symbol and returns true
; when the symbol occurs in the list. Used to check for duplicate parameters.
(define (contains? [l : (Listof Symbol)] [sym : Symbol]) : Boolean
  (cond
    [(empty? l) #f]
    [(symbol=? (first l) sym) #t]
    [else (contains? (rest l) sym)]))

; lookup function that takes a symbol and environment and returns the value binded to the symbol
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "ZNQR: name not found ~e" for)]
    [else (cond
            [(symbol=? for (Binding-name (first env))) (Binding-val (first env))]
            [else (lookup for (rest env))])]))


; TEST CASES SECTION

; simple environment used in test cases on top of top-env
(define add-to-env (list
                    (Binding 'a (NumV 1))
                    (Binding 'b (NumV 3))
                    (Binding 'c (NumV 4))
                    (Binding 'f (ClosV (list 'x 'bob) (NumC 5) mt-env))
                    (Binding 'foofunc (ClosV (list 'x) (AppC (IdC '*) (list (IdC 'x) (NumC 7))) top-env))
                    (Binding 'add-two (ClosV (list 'x) (AppC (IdC '+) (list (IdC 'x) (NumC 2))) top-env))
                    (Binding 'two-args-func (ClosV (list 'a 'b)
                                                   (AppC (IdC '+) (list (AppC (IdC '+)
                                                                              (list (IdC 'a) (IdC 'b)))
                                                                        (NumC 2))) top-env))))
(define test-env (append add-to-env top-env))


; lookup test cases
(define lookup-env (list (Binding 'banana (NumV 5)) (Binding 'apple (NumV 3)) (Binding 'orange (NumV 2))))
(check-equal? (lookup 'banana lookup-env) (NumV 5))
(check-equal? (lookup 'orange lookup-env) (NumV 2))
(check-exn (regexp (regexp-quote "ZNQR: name not found"))
           (lambda () (lookup 'notafruit lookup-env)))

; check-dup-params tests
(check-equal? (check-dup-params (list 'bob 'bab 'beb)) #f)
(check-equal? (check-dup-params (list 'beb 'bob 'beb)) #t)


; top-interp test cases
(check-equal? (top-interp '{{{a b c} -> {+ {* a b} c}} 1 2 3}) "5")
(check-equal? (top-interp '{{a b c} -> {+ {* 3 3} 3}}) "#<procedure>")
(check-equal? (top-interp '+) "#<primop>")

; primitive helper function test cases
(check-equal? (prim-helper '+ (list (NumV 3) (NumV 4))) (NumV 7))
(check-equal? (prim-helper '* (list (NumV 3) (NumV 4))) (NumV 12))
(check-equal? (prim-helper '- (list (NumV 3) (NumV 0))) (NumV 3))
(check-equal? (prim-helper '/ (list (NumV 3) (NumV 1))) (NumV 3))
(check-equal? (prim-helper '<= (list (NumV 3) (NumV 1))) (BoolV #f))
(check-equal? (prim-helper 'equal? (list (NumV 3) (NumV 3))) (BoolV #t))
(check-equal? (prim-helper 'equal? (list (BoolV #t) (BoolV #t))) (BoolV #t))
(check-equal? (prim-helper 'equal? (list (BoolV #t) (PrimV 'blah))) (BoolV #f))
(check-equal? (prim-helper 'equal? (list (BoolV #t) (NumV 3))) (BoolV #f))
(check-equal? (prim-helper 'equal? (list (NumV 4) (NumV 3))) (BoolV #f))
(check-exn (regexp (regexp-quote "ZNQR: Div by 0"))
           (lambda () (prim-helper '/ (list (NumV 1) (NumV 0)))))
(check-exn (regexp (regexp-quote "ZNQR: Invalid argument for primitive operator"))
           (lambda () (prim-helper 'blah (list (PrimV 'y) (PrimV 'x)))))
(check-exn (regexp (regexp-quote "ZNQR: Invalid primitive operator"))
           (lambda () (prim-helper 'blarg (list (NumV 1) (NumV 0)))))
(check-exn (regexp (regexp-quote "ZNQR: Invalid argument for primitive operator"))
           (lambda () (prim-helper 'blarg (list (NumV 1) (NumV 0) (NumV 3)))))

; interp test cases
(check-equal? (interp (IfThenElseC (IdC 'true) (NumC 0) (NumC 3)) test-env) (NumV 0))
(check-equal? (interp (NumC 5) mt-env) (NumV 5))
(check-equal? (interp (IfThenElseC (AppC (IdC '<=) (list (NumC 4) (NumC 5))) (NumC 0) (NumC -1)) test-env) (NumV 0))
(check-equal? (interp (IfThenElseC (AppC (IdC 'equal?) (list (NumC 4) (NumC 3))) (NumC 0) (NumC 5)) test-env) (NumV 5))
(check-exn (regexp (regexp-quote "ZNQR: Test value is not a boolean"))
           (lambda () (interp (IfThenElseC (IdC 'a) (NumC 0) (NumC 2)) test-env)))
(check-equal? (interp (AppC (IdC '+) (list (NumC 5) (NumC 4))) top-env) (NumV 9))
(check-equal? (interp (AppC (IdC '*) (list (NumC 2) (NumC 3))) top-env) (NumV 6))
(check-equal? (interp (AppC (IdC '*) (list
                                      (AppC (IdC '+) (list (NumC 3) (NumC 4)))
                                      (NumC 8)))
                      top-env)
              (NumV 56))
(check-equal? (interp (AppC (IdC 'foofunc) (list (NumC 3))) test-env) (NumV 21))
(check-equal? (interp (AppC (IdC 'foofunc) (list (AppC (IdC '*) (list (NumC 3) (NumC 4))))) test-env) (NumV 84))
(check-equal? (interp (AppC (IdC 'foofunc) (list
                                            (AppC (IdC 'add-two)
                                                  (list (NumC 5))))) test-env) (NumV 49))
(check-equal? (interp (AppC (IdC 'two-args-func) (list
                                                  (NumC 3)
                                                  (AppC (IdC 'foofunc) (list (NumC 3))))) test-env) (NumV 26))
(check-equal? (interp (LamC (list 'x) (NumC 5)) mt-env) (ClosV (list 'x) (NumC 5) mt-env))
; check lambda overwriting existing vars in the env
(check-equal? (interp (AppC (LamC (list 'b) (IdC 'b)) (list (NumC 3))) test-env)
              (NumV 3))
; check lambda takes existing vars in the env
(check-equal? (interp (AppC (LamC '() (IdC 'a)) '()) test-env)
              (NumV 1))
; nested lambda
(check-equal? (interp (AppC
                       (AppC
                        (LamC (list 'a)
                              (LamC (list 'b) (AppC (IdC '+) (list (IdC 'a) (IdC 'b)))))
                        (list (NumC 3)))
                       (list (NumC 4)))
                      top-env)
              (NumV 7))
; nested lambda but same variable overwritten
(check-equal? (interp (AppC
                       (AppC
                        (LamC (list 'a)
                              (LamC (list 'a) (AppC (IdC '+) (list (IdC 'a) (IdC 'a)))))
                        (list (NumC 3)))
                       (list (NumC 4)))
                      top-env)
              (NumV 8))
(check-exn (regexp (regexp-quote "ZNQR: not valid argument list length"))
           (lambda () (interp (AppC (IdC 'f) (list (NumC 5))) test-env)))
(check-exn (regexp (regexp-quote "ZNQR: Div by 0"))
           (lambda () (interp (AppC (IdC '/) (list (NumC 5) (NumC 0))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Invalid value for AppC"))
           (lambda () (interp (AppC (NumC 5) '()) top-env)))

; serialize test cases
(check-equal? (serialize (NumV 5)) "5")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (StringV "blah")) "\"blah\"")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (ClosV (list 'a) (NumC 3) mt-env)) "#<procedure>")

; parse test cases
(check-equal? (parse '5) (NumC 5))
(check-equal? (parse '"Hello") (StringC "Hello"))
(check-equal? (parse 'somevar) (IdC 'somevar))
(check-equal? (parse '{if {<= 0 5} 1 2}) (IfThenElseC (AppC (IdC '<=) (list (NumC 0) (NumC 5)))
                                                      (NumC 1) (NumC 2)))
; error parse test cases
(check-exn (regexp (regexp-quote "ZNQR: Parse error"))
           (lambda () (parse 'var)))
(check-exn (regexp (regexp-quote "ZNQR: Parse error"))
           (lambda () (parse '->)))
(check-exn (regexp (regexp-quote "ZNQR: Parse error"))
           (lambda () (parse '=)))
(check-exn (regexp (regexp-quote "ZNQR: Parse error"))
           (lambda () (parse '{{{}}})))
(check-exn (regexp (regexp-quote "ZNQR: Parse error"))
           (lambda () (parse '{if 'true 0})))
(check-exn (regexp (regexp-quote "ZNQR: Duplicate names error"))
           (lambda () (parse '{{x x} -> x})))
(check-exn (regexp (regexp-quote "ZNQR: Duplicate names error"))
           (lambda () (parse '{var {somevar = 2} {somevar = 3} {+ somevar somevar}})))
(check-exn (regexp (regexp-quote "ZNQR: Invalid ID error"))
           (lambda () (parse '{var {-> = 2} {somevar = 3} {+ somevar somevar}})))
(check-exn (regexp (regexp-quote "ZNQR: Invalid ID error"))
           (lambda () (parse '{{-> <-} -> {-> <- ->}})))
; lambda parsing test cases
(check-equal? (parse '{f 1}) (AppC (IdC 'f) (list (NumC 1))))
(check-equal? (parse '{{blarg blah} -> 5}) (LamC (list 'blarg 'blah) (NumC 5)))
(check-equal? (parse '{{blarg} -> {+ 4 1}}) (LamC (list 'blarg) (AppC (IdC '+) (list (NumC 4) (NumC 1)))))
(check-equal? (parse '{{} -> 5}) (LamC '() (NumC 5)))
; var assignment test cases
(check-equal? (parse '{var {somevaridk = 2} {anothervar = 5} {+ somevaridk anothervar}})
              (AppC (LamC (list 'somevaridk 'anothervar)
                          (AppC (IdC '+)
                                (list (IdC 'somevaridk) (IdC 'anothervar))))
                    (list (NumC 2) (NumC 5))))
(check-equal? (parse '{var {somevaridk = 2} {+ somevaridk somevaridk}})
              (AppC (LamC (list 'somevaridk)
                          (AppC (IdC '+)
                                (list (IdC 'somevaridk) (IdC 'somevaridk))))
                    (list (NumC 2))))
