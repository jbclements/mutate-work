#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)

; Assignment 3 completed in full.

; represents an arithmetic language that supports + and *
(define-type ExprC (U NumC ifC idC appC lamC strC))
; represents a number
(struct NumC ([n : Real]) #:transparent)
; represents an if statement
(struct ifC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
; represents an identifier
(struct idC ([s : Symbol]) #:transparent)
; represents a function application
(struct appC ([body : ExprC] [args : (Listof ExprC)]) #:transparent)
; represents a lambda expression
(struct lamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
; represents a string statement
(struct strC ([str : String]) #:transparent)


; defines an environment
(define-type Env (Listof Binding))
; defines an empty environment
(define mt-env '())
; defines how to extend an environment
(define extend-env cons)
; define a binding of a name to a value
(struct Binding ([name : Symbol] [val : Value]) #:transparent)

; defines legal values
(define-type Value (U NumV BoolV StrV ClosV PrimV))
; represents a Real number value
(struct NumV ([n : Real]) #:transparent)
; represents a Boolean value
(struct BoolV ([bool : Boolean]) #:transparent)
; represents a String value
(struct StrV ([str : String]) #:transparent)
; represents a closures
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
; represents a primative operator
(struct PrimV ([op : Symbol]) #:transparent)


; a top level environment containing basic functionality
(define top-env (list
                 (Binding 'true (BoolV #t))
                 (Binding 'false (BoolV #f))
                 (Binding '+ (PrimV '+))
                 (Binding '/ (PrimV '/))
                 (Binding '* (PrimV '*))
                 (Binding '- (PrimV '-))
                 (Binding '<= (PrimV '<=))
                 (Binding 'equal? (PrimV 'equal?))))

;;> interp should be at the top as per syllabus

; parses an Sexp into a ExprC
(define (parse [exp : Sexp]) : ExprC
  (match exp
    [(list (? symbol? s) '= assign) (parse assign)]
    [(list (list (? symbol? s)...) '-> body) (if (check-duplicates (cast s (Listof Symbol)))
                                                 (error 'interp "ZNQR: illegal duplicate parameter names")
                                                 (lamC (cast s (Listof Symbol)) (parse body)))]
    [(list 'if parts ...) (if (equal? (length parts) 3)
                             (ifC (parse (first parts)) (parse (second parts)) (parse (third parts)))
                             (error 'parse "ZNQR: incorrect if formatting"))]
    [(list 'var args ... body) (appC (desugar body (cast args (Listof Sexp)))
                                     (map parse (cast args (Listof Sexp))))]
    [(list body args ...) (appC (parse body) (map parse args))]
    [(? real? n) (NumC n)]
    [(? string? str) (strC str)]
    [(? symbol? s) (if (or (equal? s 'if) (equal? s '=) (equal? s 'var) (equal? s '->))
                       (error 'parse "ZNQR: ~e is not a valid identifier"  s)
                       (idC s))]))

; desugars a var def into a lambda
(define (desugar [body : Sexp] [args : (Listof Sexp)]) : ExprC
  (define vars (map (lambda ([arg : Sexp]) (match arg [(list (? symbol? s) '= args ...) s])) args))
  (if (check-duplicates vars)
      (error 'desugar "ZNQR: illegal duplicate parameter names")
      (if (and (empty? vars) (contains-eq? body))
          (error 'desugar "ZNQR: function definition requires a body")
          (if (contains-illegal? vars)
              (error 'contains-illegal? "ZNQR: contains illegal identifier name")
              (lamC vars (parse body))))))

; checks if the body of a var contains a var assignment
(define (contains-eq? [s : Sexp]) : Boolean
  (match s
    [(list name '= other ...) #t]
    [else #f]))

; checks if a sugared argument is of a resevered keyword
(define (contains-illegal? [s : (Listof Symbol)]) : Boolean
  (cond
    [(empty? s) #f]
    [(or (equal? (first s) 'if) (equal? (first s) '=) (equal? (first s) 'var) (equal? (first s) '->)) #t]
    [else (contains-illegal? (rest s))]))


; evalutes a given ExprC within an environment and returns a Value
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(NumC n) (NumV n)]
    [(strC str) (StrV str)]
    [(lamC args body) (ClosV args body env)]
    [(appC f a) (define f-value (interp f env))
                (match f-value
                  [(ClosV params body cur-env)
                   (define new-env (if (equal? (length a) (length params))
                                       (append (map (lambda ([name : Symbol] [val : ExprC])
                                                              (Binding name (interp val env))) params a) cur-env)
                                       (error 'interp "ZNQR: number of arguments supplied does not match parameters")))
                   (interp body new-env)]
                  [(PrimV op) (prim-interp op a env)]
                  [else (error 'interp "ZNQR: cannot invoke non-function value")])]
    [(ifC test then else) (define check (interp test env))
                         (if (BoolV? check)
                             (if (BoolV-bool check) (interp then env) (interp else env))
                             (error 'interp "ZNQR: test value for if must be boolean"))]
    [(idC x) (lookup x env)]))

; handles primative value interpreting
(define (prim-interp [op : Symbol] [args : (Listof ExprC)] [env : Env]) : Value
  (if (equal? (length args) 2)
      (let ([left (interp (first args) env)])
        (let ([right (interp (second args) env)])
          (match op
            ['+ (if (and (NumV? left) (NumV? right))
                    (NumV (+ (NumV-n left) (NumV-n right)))
                    (error 'interp "ZNQR: Both operands of + must be numeric"))]
            ['/ (if (and (NumV? left) (NumV? right))
                    (if (equal? (NumV-n right) 0)
                        (error 'interp "ZNQR: Cannot divide by 0")
                        (NumV (/ (NumV-n left) (NumV-n right))))
                    (error 'interp "ZNQR: Both operands of / must be numeric"))]
            ['* (if (and (NumV? left) (NumV? right))
                    (NumV (* (NumV-n left) (NumV-n right)))
                    (error 'interp "ZNQR: Both operands of * must be numeric"))]
            ['- (if (and (NumV? left) (NumV? right))
                    (NumV (- (NumV-n left) (NumV-n right)))
                    (error 'interp "ZNQR: Both operands of - must be numeric"))]
            ['<= (if (and (NumV? left) (NumV? right))
                     (BoolV (<= (NumV-n left) (NumV-n right)))
                     (error 'interp "ZNQR: Both operands of <= must be numeric"))]
            ['equal? (if (or (PrimV? left) (PrimV? right) (ClosV? left) (ClosV? right))
                         (BoolV #f)
                         (BoolV (equal? left right)))])))
      (error 'interp "ZNQR: incorrect number of args to binary operator")))

; looks up a value from a given a name from an environment
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "ZNQR: name not found: ~e" for)]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (Binding-val (first env))]
            [else (lookup for (rest env))])]))


; takes a Value and returns a string representation of it
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (~v n)]
    [(BoolV bool) (if bool "true" "false")]
    [(StrV str) (~v str)]
    [(ClosV a b c) "#<procedure>"]
    [(PrimV op) "#<primop>"]))


; takes in a "program and returns its value"
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))


; Test Cases -----------------------------------------------------
; parse and helpers
(check-equal? (parse '{{a b c} -> 3}) (lamC '(a b c) (NumC 3)))
(check-equal? (parse '"Hello") (strC "Hello"))
(check-equal? (parse '9) (NumC 9))
(check-equal? (parse '{+ 3 4}) (appC (idC '+) (list (NumC 3) (NumC 4))))
(check-equal? (parse '{a}) (appC (idC 'a) '()))
(check-equal? (parse 'true) (idC 'true))
(check-equal? (parse '{if true 4 19}) (ifC (idC 'true) (NumC 4) (NumC 19)))
(check-equal? (parse '{{{z y} -> {+ z y}} {+ 9 14} 98}) (appC
                                                         (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
                                                         (list (appC (idC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}}) (appC
                                                         (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
                                                         (list (appC (idC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-exn (regexp (regexp-quote "ZNQR: '= is not a valid identifier"))
           (lambda () (parse '{{=} -> {+ 3 =}})))
(check-exn (regexp (regexp-quote "ZNQR: incorrect if formatting"))
           (lambda () (parse '{if 1 2})))
(check-exn (regexp (regexp-quote "ZNQR: illegal duplicate parameter names"))
           (lambda () (parse '{var {z = {{} -> 3}} {z = 9} {z}})))
(check-exn (regexp (regexp-quote "ZNQR: function definition requires a body"))
           (lambda () (parse '{var {c = ""}})))
(check-exn (regexp (regexp-quote "ZNQR: contains illegal identifier name"))
           (lambda () {parse '{var {-> = ""} "World"}}))

(check-equal? (desugar '{+ z y} '{{z = {+ 9 14}} {y = 98}}) (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y)))))

(check-equal? (contains-eq? '(b = 12)) #t)
(check-equal? (contains-eq? '(= a 12)) #f)
(check-equal? (contains-eq? '()) #f)

(check-equal? (contains-illegal? (list 'a 'b 'r)) #f)
(check-equal? (contains-illegal? '()) #f)
(check-equal? (contains-illegal? (list 'if 'b 'r)) #t)

; interp and helpers
(check-equal? (interp (appC (lamC '(a b) (idC 'a)) (list (NumC 1) (NumC 2))) top-env) (NumV 1))
(check-equal? (interp (appC (idC '+) (list (NumC 1) (NumC 2))) top-env) (NumV 3))
(check-equal? (interp (appC (idC '/) (list (NumC 4) (NumC 2))) top-env) (NumV 2))
(check-equal? (interp (appC (idC '+) (list (NumC 1) (appC (idC '+) (list (NumC 3) (NumC 5)))))
                      top-env) (NumV 9))
(check-equal? (interp (appC (lamC '(a b) (appC (idC '+) (list (idC 'a) (idC 'b))))
                            (list (NumC 1) (NumC 2))) top-env) (NumV 3))
(check-equal? (interp (appC (idC '<=) (list (NumC 1) (NumC 2))) top-env) (BoolV #t))
(check-equal? (interp (appC (idC '<=) (list (NumC 4) (NumC 2))) top-env) (BoolV #f))
(check-equal? (interp (appC (idC 'equal?) (list (NumC 4) (idC 'hello)))
                      (cons (Binding 'hello (StrV "hello")) top-env)) (BoolV #f))
(check-equal? (interp (appC (idC 'equal?) (list (idC 'hello) (idC 'hello)))
                      (cons (Binding 'hello (StrV "hello")) top-env)) (BoolV #t))
(check-equal? (interp (appC (idC 'equal?) (list (lamC '(a b) (idC 'a))
                                                (lamC '(a b) (idC 'a)))) top-env) (BoolV #f))
(check-equal? (interp (ifC
                       (appC (idC '<=) (list (NumC 9) (NumC 2)))
                       (NumC 7)
                       (appC (idC '+) (list (NumC 1) (NumC 2)))) top-env) (NumV 3))
(check-equal? (interp (ifC
                       (idC 'true)
                       (NumC 7)
                       (appC (idC '+) (list (NumC 1) (NumC 2)))) top-env) (NumV 7))
(check-equal? (interp (ifC
                       (appC (idC '<=) (list (NumC 1) (NumC 2)))
                       (appC (idC '<=) (list (NumC 12) (NumC 2)))
                       (appC (idC '+) (list (NumC 1) (NumC 2)))) top-env) (BoolV #f))
(check-equal? (interp (appC (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
                            (list (appC (idC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env) (NumV 121))
(check-exn (regexp (regexp-quote "ZNQR: incorrect number of args to binary operator"))
           (lambda () (interp (appC (idC '+) (list (NumC 1))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Both operands of + must be numeric"))
           (lambda () (interp (appC (idC '+) (list (NumC 1) (strC "Hi"))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Both operands of - must be numeric"))
           (lambda () (interp (appC (idC '-) (list (NumC 1) (strC "Hi"))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Both operands of / must be numeric"))
           (lambda () (interp (appC (idC '/) (list (NumC 1) (strC "Hi"))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Both operands of * must be numeric"))
           (lambda () (interp (appC (idC '*) (list (NumC 1) (strC "Hi"))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Both operands of <= must be numeric"))
           (lambda () (interp (appC (idC '<=) (list (NumC 1) (strC "Hi"))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: Cannot divide by 0"))
           (lambda () (interp (appC (idC '/) (list (NumC 1) (NumC 0))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: test value for if must be boolean"))
           (lambda () (interp (ifC (NumC 1) (NumC 2) (NumC 3)) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: cannot invoke non-function value"))
           (lambda () (interp (appC (NumC 3) (list (NumC 1) (NumC 0))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: number of arguments supplied does not match parameters"))
           (lambda () (interp (appC (lamC '(a b) (idC 'a)) (list (NumC 1))) top-env)))

(define myenv (list (Binding 'hello (NumV 3)) (Binding 'nine (BoolV #t)) (Binding 'pop (StrV "Hi"))))
(check-equal? (lookup 'hello myenv) (NumV 3))
(check-equal? (lookup 'pop myenv) (StrV "Hi"))
(check-exn (regexp (regexp-quote "ZNQR: name not found: 'nope"))
           (lambda () (lookup 'nope myenv)))

; serialize tests
(check-equal? (serialize (NumV 3)) "3")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (StrV "hello")) "\"hello\"")
(check-equal? (serialize (ClosV (list 'a 'r) (NumC 2) '())) "#<procedure>")
(check-equal? (serialize (PrimV '+)) "#<primop>")

; top-interp
(check-equal? (top-interp '{var {z = {+ 9 14}} {y = 98} {+ z y}}) "121")
(check-equal? (top-interp '{{{x} -> {* x 2}} 5}) "10")
(check-equal? (top-interp '{var {x = {if {<= 5 2} {+ 3 4} {- 2 0}}} {y = true} {if y x 45}}) "2")
(check-equal? (top-interp '{var {+ 2 4}}) "6")
(check-equal? (top-interp '{{{} -> 10}}) "10")
(check-equal? (top-interp '{{{} -> "Hello"}}) "\"Hello\"")
(check-equal? (top-interp '{{{+} -> {* + +}} 14}) "196")
(check-exn (regexp (regexp-quote "ZNQR: illegal duplicate parameter names"))
           (lambda () (top-interp '{{x x} -> {+ x x}})))


