#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)

;;> do not put name on submission please

;This project is done by Angaddeep Bains
;The project is completed. All tests passed.

;; this macro defines a "tstruct" form that's just
;; like "struct" but automatically inserts the #:transparent tag.
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
      (struct name fields #:transparent)]))

(define-type ExprC (U IdC RealC StringC BooleanC IfC AppC LamC))
  (tstruct IdC ([s : Symbol]))
  (tstruct RealC ([d : Real]))
  (tstruct StringC ([s : String]))
  (tstruct BooleanC ([b : Boolean]))
  (tstruct IfC ([condExpr : ExprC] [thenExpr : ExprC] [elseExpr : ExprC]))
  (tstruct AppC ([body : ExprC] [args : (Listof ExprC)]))
  (tstruct LamC ([params : (Listof Symbol)] [body : ExprC]))
(define-type Value (U RealV BooleanV StringV ClosureV PrimOpV))
  (tstruct RealV ([d : Real]))
  (tstruct BooleanV ([b : Boolean]))
  (tstruct StringV ([s : String]))
  (tstruct ClosureV ([vars : (Listof Symbol)] [body : ExprC] [env : Environment]))
  (tstruct PrimOpV ([op : (-> Value Value Value)]))

; Stores info about any variables we found so far.
(define-type Environment (Immutable-HashTable Symbol Value))

; Combines parsing and evaluation.
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; Interprets an expression, with a given environment.
(define (interp [expr : ExprC] [env : Environment]) : Value
  (match expr
    [(IdC s) (get-env-var env s)]
    [(RealC d) (RealV d)]
    [(StringC s) (StringV s)]
    [(BooleanC b) (BooleanV b)]
    [(IfC conditionExpr thenExpr elseExpr)
      (let ([condition : Value (interp conditionExpr env)])
        (if (BooleanV? condition)
          (if (BooleanV-b condition) (interp thenExpr env) (interp elseExpr env))
          (error (string-append "ZNQR: Not a boolean: " (~v condition)))))]
    [(LamC params body) (ClosureV params body env)]
    [(AppC bodyExpr argsExpr)
      (let*
        ([args : (Listof Value)
          (map (lambda ([argExpr : ExprC]) (interp argExpr env)) argsExpr)]
        [bodyVal : Value (interp bodyExpr env)]
        [substitutor : (-> Symbol Value Environment Environment)
                (lambda
                  ([param : Symbol] [arg : Value] [envCurrent : Environment]) : Environment
                  (set-env-var envCurrent param arg))])
        (match bodyVal
            [(ClosureV params body envForClosure) (let
              ([envNew : Environment ((inst foldl Symbol Value Environment) substitutor envForClosure params args)])
              (interp body envNew))]
            [(PrimOpV op) (op (first args) (second args))]
            [else (error (string-append "ZNQR: Invalid body for application: " (~v bodyVal)))]))]))

; Parses an expression.
(define (parse [s : Sexp]) : ExprC
  (cond
    [(is-variable? s) (IdC (cast s Symbol))]
    [(real? s) (RealC s)]
    [(string? s) (StringC s)]
    [(and (list? s) (equal? (length s) 4) (equal? (first s) 'if))
      (let (
        [condition : ExprC (parse (second s))]
        [thenBranch : ExprC (parse (third s))]
        [elseBranch : ExprC (parse (fourth s))])
        (IfC condition thenBranch elseBranch))]
    [(and (list? s)
      (equal? (length s) 3)
      (equal? (second s) '->)
      (list? (first s)))
      (LamC (parse-params (cast (first s) (Listof Sexp))) (parse (third s)))]
    [(and (list? s) (>= (length s) 2) (equal? (first s) 'var))
      (match s
        [(list 'var (list params '= argExprs) ... body)
          (AppC
            (LamC
              (parse-params (cast params (Listof Sexp)))
              (parse body))
            ((inst map ExprC Sexp) parse (cast argExprs (Listof Sexp))))]
        [else (error (string-append "ZNQR: invalid var expression: " (~v s)))])]
    [(and (list? s) (not (empty? s)) (not (is-keyword? (first s))))
      (let ([firstExpr : ExprC (parse (first s))] [argsExpr : (Listof ExprC) (map parse (rest s))])
        (if
          (and
            (LamC? firstExpr)
            (not (equal? (length (LamC-params firstExpr)) (length argsExpr))))
          (error (string-append "ZNQR: bad number of arguments for lambda: " (~v s)))
          (AppC firstExpr argsExpr)))]
    [else (error (string-append "ZNQR: Bad input: " (~v s)))]))

; Converts Value - the result of interpreter to string according to the assignment requirement.
(define (serialize [v : Value]) : String
  (match v
    [(RealV d) (~v d)]
    [(BooleanV #t) "true"]
    [(BooleanV #f) "false"]
    [(StringV s) s]
    [(ClosureV _ _ _) "#<procedure>"]
    [(PrimOpV _) "#<primop>"]))

;; Parse helpers.
; Returns true of alphanumeric symbol is a keyword of ZNQR3.
(define (is-keyword? [s : Sexp]) : Boolean
  (or
    (equal? s 'if)
    (equal? s 'var)
    (equal? s '->)
    (equal? s '=)))

; Returns #t if Sexp can be a variable name in ZNQR3.
(define (is-variable? [s : Sexp]) : Boolean
  (and
    (symbol? s)
    (not (is-keyword? s))
    (not (real? s))))

; parses expression {id = ...} from var syntax and
; returns array of symbols - parameters to lambda expression.
(define (parse-params [params : (Listof Sexp)]) : (Listof Symbol)
  (if (check-duplicates params)
    (error (string-append "ZNQR: duplicate parameters: " (~v params)))
    (if
      (andmap is-variable? params)
      (cast params (Listof Symbol))
      (error (string-append "ZNQR: bad parameters: " (~v params))))))

;; Interpretation helpers
; Primitive operators
(define (apply-arithmetic [op : (-> Real Real Real)] [l : Value] [r : Value]) : Value
  (if
    (and (RealV? l) (RealV? r))
    (RealV (op (RealV-d l) (RealV-d r)))
    (error (string-append "ZNQR: unexpected left or right argument for arithmetic binop: " (~v l) ", " (~v r)))))
(define (sum-op [a : Value] [b : Value]) : Value (apply-arithmetic + a b))
(define (minus-op [a : Value] [b : Value]) : Value (apply-arithmetic - a b))
(define (mult-op [a : Value] [b : Value]) : Value (apply-arithmetic * a b))
(define (div-op [a : Value] [b : Value]) : Value
  (if
    (and (RealV? b) (zero? (RealV-d b)))
    (error "ZNQR: Division by zero")
    (apply-arithmetic / a b)))
(define (leq-op [a : Value] [b : Value]) : Value
  (if
    (and (RealV? a) (RealV? b))
    (BooleanV (<= (RealV-d a) (RealV-d b)))
    (error (string-append "ZNQR: Bad type for leq parameters: " (~v (list a b))))))
(define (equal-op [a : Value] [b : Value]) : Value
  (let ([result : Boolean (cond
    [(and (RealV? a) (RealV? b)) (equal? (RealV-d a) (RealV-d b))]
    [(and (StringV? a) (StringV? b)) (equal? (StringV-s a) (StringV-s b))]
    [(and (BooleanV? a) (BooleanV? b)) (equal? (BooleanV-b a) (BooleanV-b b))]
    [else #f])])
    (BooleanV result)))

;; Environment procedures.
(define (set-env-var [env : Environment] [varName : Symbol] [varValue : Value]) : Environment
  (hash-set env varName varValue))

(define (get-env-var [env : Environment] [varName : Symbol])
  (hash-ref env varName
    (lambda () (error (string-append "ZNQR: symbol not found: "
      (~v varName)
      " in environment: "
      (~v env))))))

(define top-env : Environment (hash
  'true (BooleanV #t)
  'false (BooleanV #f)
  '+ (PrimOpV sum-op)
  '- (PrimOpV minus-op)
  '* (PrimOpV mult-op)
  '/ (PrimOpV div-op)
  '<= (PrimOpV leq-op)
  'equal? (PrimOpV equal-op)))

; ;;;; TESTS ;;;
; (: is-variable? (Sexp -> Boolean))
(check-equal? (is-variable? 'a) #t)
(check-equal? (is-variable? 'Aabc) #t)
(check-equal? (is-variable? '123) #f)
; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (: is-keyword? (Sexp -> Boolean))
(check-equal? (is-keyword? 'a) #f)
(check-equal? (is-keyword? 'if) #t)
(check-equal? (is-keyword? 'var) #t)
; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (: parse-params ((Listof Sexp) -> (Listof Symbol)))
(check-equal? (parse-params '(a b c)) (list 'a 'b 'c))
(check-exn
  (regexp (regexp-quote "ZNQR: duplicate parameters: '(x y x)"))
  (lambda () (parse-params (list 'x 'y 'x))))
; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (: parse (Sexp -> ExprC))
; sample from Krishnamurthi (chapter 2).
(check-equal?
  (parse '(- (/ 1 2) (* 4 3)))
  (AppC (IdC '-) (list (AppC (IdC '/) (list (RealC 1) (RealC 2))) (AppC (IdC '*) (list (RealC 4) (RealC 3))))))

; Modified test for other types of arithmetic binary operations.
(check-equal?
  (parse '(+ (* 1 2) (+ 2 3)))
  (AppC (IdC '+) (list (AppC (IdC '*) (list (RealC 1) (RealC 2))) (AppC (IdC '+) (list (RealC 2) (RealC 3))))))
; Checking other variants of expression.
(check-equal? (parse "hello") (StringC "hello"))
(check-equal? (parse 'true) (IdC 'true))
(check-equal? (parse 'false) (IdC 'false))
(check-equal? (parse 1) (RealC 1))
(check-equal? (parse 'x) (IdC 'x))
(check-equal? (parse '{+ x 1}) (AppC (IdC '+) (list (IdC 'x) (RealC 1))))
(check-equal? (parse '{if true x y}) (IfC (IdC 'true) (IdC 'x) (IdC 'y)))
(check-equal?
  (parse '{{{x} -> {* 2 x}} 3})
  (AppC (LamC '(x) (AppC (IdC '*) (list (RealC 2) (IdC 'x)))) (list (RealC 3))))
(check-equal? (parse '{{} -> 42}) (LamC '() (RealC 42)))
(check-exn
  (regexp (regexp-quote "ZNQR: bad number of arguments for lambda: '(((x) -> (* 2 x)) 3 2)"))
  (lambda () (parse '{{{x} -> {* 2 x}} 3 2})))
(check-equal?
  (parse '{{z y} -> {+ z y}})
  (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y)))))
(check-exn (regexp (regexp-quote "ZNQR: duplicate parameters: '(z z)")) (lambda () (parse '{{z z} -> {z + z}})))
(check-exn (regexp (regexp-quote "ZNQR: bad parameters: '(1 z)")) (lambda () (parse '{{1 z} -> {z + z}})))
(check-equal?
  (parse '{var {z = {* 9 14}} {y = 98} {+ z y}})
  (AppC
    (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
    (list (AppC (IdC '*) (list (RealC 9) (RealC 14))) (RealC 98))))
(check-equal? (parse '{var {+ 1 2}})
  (AppC (LamC '() (AppC (IdC '+) (list (RealC 1) (RealC 2)))) '()))
(check-exn (regexp (regexp-quote "ZNQR: Bad input: '()")) (lambda () (parse '{})))
(check-exn (regexp (regexp-quote "ZNQR: bad parameters: '(if)")) (lambda () (parse '{var {if = 1} {+ if 2}})))
(check-exn
  (regexp (regexp-quote "ZNQR: invalid var expression: '(var (x = 1 2) (x))"))
  (lambda () (parse '{var {x = 1 2} {x}})))
(check-exn
  (regexp (regexp-quote "ZNQR: Bad input: '="))
  (lambda () (parse '{var {x = 1}})))


;; Interpreter procedures tests.
; Simple operators.
(check-equal? (sum-op (RealV 1.0) (RealV 2.0)) (RealV 3.0))
(check-exn
  (regexp (regexp-quote "ZNQR: unexpected left or right argument for arithmetic binop: "))
  (lambda () (sum-op (StringV "first") (StringV "second"))))
(check-equal? (minus-op (RealV 1.0) (RealV 2.0)) (RealV -1.0))
(check-equal? (mult-op (RealV 2.0) (RealV 8.0)) (RealV 16.0))
(check-equal? (div-op (RealV 1.0) (RealV 2.0)) (RealV 0.5))
(check-exn (regexp (regexp-quote "ZNQR: Division by zero")) (lambda () (div-op (RealV 1.0) (RealV 0.0))))
(check-equal? (equal-op (RealV 1.0) (RealV 1.0)) (BooleanV #t))
(check-equal? (equal-op (RealV 1.0) (RealV 2.0)) (BooleanV #f))
(check-equal? (equal-op (RealV 1.0) (StringV "1.0")) (BooleanV #f))
(check-equal? (equal-op (StringV "1.0") (StringV "1.0")) (BooleanV #t))
(check-equal? (equal-op (BooleanV #f) (BooleanV #f)) (BooleanV #t))
(check-equal? (equal-op (BooleanV #f) (BooleanV #t)) (BooleanV #f))
(check-equal? (equal-op (BooleanV #f) (ClosureV '(x y) (IdC 'x) top-env)) (BooleanV #f))
(check-equal? (leq-op (RealV 1.0) (RealV 2.0)) (BooleanV #t))
(check-equal? (leq-op (RealV 2.0) (RealV 1.0)) (BooleanV #f))
(check-exn
  (regexp (regexp-quote "ZNQR: Bad type for leq parameters: "))
  (lambda () (leq-op (BooleanV #f) (BooleanV #t))))
(check-exn
  (regexp (regexp-quote "ZNQR: Invalid body for application: (RealV 1)"))
  (lambda () (interp (AppC (LamC '(x) (AppC (IdC 'x) '())) (list (RealC 1))) top-env)))

; Environment
(check-equal? (set-env-var (hash) 'a (StringV "avalue")) (hash 'a (StringV "avalue")))
(check-equal? (get-env-var top-env '+) (PrimOpV sum-op))
(check-exn (regexp (regexp-quote "ZNQR: symbol not found: '!=")) (lambda () (get-env-var top-env '!=)))

;; Top level tests.
; serialize
(check-equal? (serialize (RealV 1.0)) "1.0")
(check-equal? (serialize (BooleanV #t)) "true")
(check-equal? (serialize (BooleanV #f)) "false")
(check-equal? (serialize (StringV "string")) "string")
(check-equal? (serialize (ClosureV '(x y) (IdC 'x) top-env)) "#<procedure>")
(check-equal? (serialize (PrimOpV equal-op)) "#<primop>")

; interp
(check-equal? (top-interp 'true) "true")
(check-exn
  (regexp (regexp-quote "ZNQR: symbol not found: 'dummy-var"))
  (lambda () (interp (IdC 'dummy-var) top-env)))
(check-equal? (interp (RealC 123.45) top-env) (RealV 123.45))
(check-equal?
  (interp
    (AppC (LamC (list 'z 'y)
      (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
      (list (AppC (IdC '*) (list (RealC 9) (RealC 14))) (RealC 98))) top-env) (RealV 224))
(check-equal? (interp (AppC (IdC '+) (list (RealC 2) (RealC 20))) top-env) (RealV 22))
(check-equal? (interp (AppC (IdC '-) (list (RealC 13) (RealC 67))) top-env) (RealV -54))
(check-equal? (interp (AppC (IdC '*) (list (RealC 32) (RealC 20))) top-env) (RealV 640))
(check-equal? (interp (AppC (IdC '/) (list (RealC 2) (RealC 20))) top-env) (RealV 1/10))
(check-equal? (interp (AppC (IdC '<=) (list (RealC 2) (RealC 1))) top-env) (BooleanV #f))
(check-equal? (interp (AppC (IdC 'equal?) (list (RealC 1.0) (RealC 2.0))) top-env) (BooleanV #f))
(check-equal? (interp (LamC (list 'x 'y) (IdC 'x)) top-env) (ClosureV '(x y) (IdC 'x) top-env))
(check-equal? (interp (StringC "123") top-env) (StringV "123"))
(check-equal? (interp (IfC (BooleanC #t) (RealC 1) (RealC 2)) top-env) (RealV 1))
(check-equal? (interp (IfC (BooleanC #f) (RealC 1) (RealC 2)) top-env) (RealV 2))
(check-exn
  (regexp (regexp-quote "ZNQR: Not a boolean: (RealV 123)"))
    (lambda () (interp (IfC (RealC 123) (RealC 1) (RealC 2)) top-env)))
(check-equal?
  (interp (AppC (LamC (list 'x) (AppC (IdC '*) (list (RealC 2) (IdC 'x))))
  (list (RealC 3))) top-env) (RealV 6))

; top-interp
(check-equal? (top-interp '{+ 1 2}) "3")
(check-equal? (top-interp '(((s) -> (s)) (((minus) -> (() -> (minus 13 6))) ((x y) -> (+ x (* -1 y)))))) "7")
(check-exn (regexp (regexp-quote "ZNQR: Division by zero")) (lambda () (top-interp '{/ 42 {- 42 42}})))
(check-equal? (top-interp '{if {<= 2 3} 1 {/ 1 0}}) "1")
(check-equal? (top-interp '(((/) -> (* / /)) 7)) "49")
(check-equal? (top-interp '(var (+ = -) (- = +) (+ 3 (- 6 4)))) "-7")
