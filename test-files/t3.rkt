;;> Testfail: expected exception with message containing JILI on test expression: '(top-interp '(((=> 3)) 4 5))
;;> Testfail: expected exception with message containing user-error on test expression: '(top-interp '(+ 4 (error "1234")))
;;> Testfail: expected exception with message containing user-error on test expression: '(top-interp '((e => (e e)) error))
;;> Testfail: while evaluating (begin (parse (quote (if (=> (=> ((=> (var ((a = (=> (if (((var ((/ = ((if (var ((- = (var ((+ = (if (if true (true false null + => false) (- * / => "Hello")) (null (equal? <= => 0) ("World" (var ((true = +)) in (1 (if "" (var ((false = "Hello")) in (var ((null = -1)) in (if 2.2 (if (var () in "") - ((((var () in /) -22/7) "World") *)) (var () in 0)))) (if (var () in (a => (if (if <= a -1) 1 "World"))) "Hello" equal?)) b)) c d) e f) g))) in h)) (* = i)) in j) k l))) (equal? = m) (<= = n)) in o))) p q))) (b = r) (c = s) (d = t)) in u))))) v w))) #t):
;  parse: JILI Invalid Syntax
;;> Testfail: expected exception with message containing JILI on test expression: '(parse '(var ((=> = "")) in "World"))
#lang typed/racket

(require typed/rackunit)
(require racket/format)

;;> Note, printing out the expression that caused an error when an error is raised
;;>   is extremely helpful for understanding what went wrong. Take a look at the definition
;;>   of error in the docs and "~v"
#|implemented all new functionality|#

;defining type ExprC
(define-type ExprC (U NumC StrC AppC IdC IfC LamC))
(struct NumC ([n : Real]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IdC ([name : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct LamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)

;defining type Value
(define-type Value (U NumV BoolV BoolOpV StrV CloV PrimOpV ErrorV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
;;> BoolOpVs are unnecessary. All that is needed to handle them is PrimOpVs
;;>   since the logic to resolve them is so similar
(struct BoolOpV ([o : Symbol]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct CloV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV ([o : Symbol]) #:transparent)
;;> Similarly to BoolOpVs, all we neeed are PrimOpVs to handle error
(struct ErrorV ([v : Any]) #:transparent)

;define binding
(struct Bind ([s : Symbol] [v : Value]) #:transparent)

;define env
(struct Env ([b : (Listof Bind)]) #:transparent)

;define top-env
(define top-env (Env (list (Bind '+ (PrimOpV '+))
                           (Bind '* (PrimOpV '*))
                           (Bind '- (PrimOpV '-))
                           (Bind '/ (PrimOpV '/))
                           (Bind 'true (BoolV true))
                           (Bind 'false (BoolV false))
                           (Bind 'equal? (BoolOpV 'equal?))
                           (Bind '<= (BoolOpV '<=))
                           (Bind 'error (ErrorV '_)))))


;takes an Sexp and returns a Real
(: top-interp (Sexp -> String))
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

;interpret ExprC AST returns a number ***from the book- still needs to be altered for JILI
(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    [(IdC n) (lookup n env)]
    ;;> Missing error handling for function applications of non-functions (e.x. '(3))
    [(AppC f a) (define f-value (interp f env))
                ;;> Take a look at the definition of map. This function will be more clean than for/list:
                (define args-to-values (for/list: : (Listof Value) ([x a]) (interp x env)))
                (match f-value
                  [(PrimOpV s) #:when (= (length args-to-values) 2)
                               (match* ((first args-to-values) (second args-to-values))
                                 [((NumV num1) (NumV num2)) #:when (false? (and (equal? s '/) (= num2 0)))
                                  (NumV ((apply-primitive f-value) num1 num2))]
                                 [(_ _) (error 'interp "JILI Invalid Syntax")]
;;> (AUTOCOMMENT) This line contains nothing but close parens:
                                 )]

                  [(BoolOpV s) #:when (and (= (length args-to-values) 2) (equal? s '<=))
                               (match* ((first args-to-values) (second args-to-values))
                                 [((NumV num1) (NumV num2))
                                  (BoolV (<= num1 num2))]
                                 [(_ _) (error 'interp "JILI Invalid Syntax")]
;;> (AUTOCOMMENT) This line contains nothing but close parens:
                                 )]

                  [(BoolOpV s) #:when (and (= (length args-to-values) 2) (equal? s 'equal?))
                               (match* ((first args-to-values) (second args-to-values))
                                 [((CloV arg b e) (PrimOpV p)) (BoolV false)]
                                 [((CloV arg b e) (CloV arg2 b2 e2)) (BoolV false)]
                                 [((PrimOpV p) (PrimOpV p2)) (BoolV false)]
                                 [((PrimOpV p) (CloV arg b e)) (BoolV false)]
                                 ;;> Note that equal? does a deep comparison for our defined structs
                                 ;;>   and handles arguments of differing types correctly. Thus you can simply
                                 ;;>   use racket's equal? instead of the manual checks above in addition to equal?
                                 [(_ _) (BoolV (equal? (first args-to-values) (second args-to-values)))]
;;> (AUTOCOMMENT) This line contains nothing but close parens:
                                 )]

                  [(CloV a b e) (interp b
                                        (Env (append (Env-b
                                                      (newBind (CloV-args f-value) args-to-values))
                                                     (Env-b e))))]
                  ;;> When encountering an "ErrorV" or rather an 'error PrimOpV, you should just directly
                  ;;>   raise the error in that moment. Do not pass it up to serialize it.
                  ;;>   Note that when raising an error, you must include the string "user-error"
                  [(ErrorV v) #:when (= (length args-to-values) 1) (ErrorV (first args-to-values))])]
    [(IfC test then else) (define val (interp test env))
                          (match val
                            [(BoolV f) #:when (false? f) (interp else env)]
                            [(BoolV t) (interp then env)]
                            [_ (error 'interp "JILI Invalid Syntax")])]
    [(LamC a b) (CloV a b env)]))

;accepts an Sexp and parses to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)] ;NumC case

    [(? symbol? s) #:when (false? (member s '(if in => var))) (IdC s)] ;IdC case

    [(? string? s) (StrC s)] ;StrC case

    [(list 'if test then else) (IfC (parse test) (parse then) (parse else))] ;{if Expr Expr Expr}

    [(list 'var
           (list (list (? symbol? params) '= exprs) ...)
           ;;> This does not actually check if the parameters are one of the reserved symbols
           ;;>   If you hover your mouse over params, you can see it is a list of symbols, which
           ;;>   makes sense based on the match statement. Thus params will never be one of the
           ;;>   reserved symbols. A helper function would be extremeley useful here
           'in body) #:when (false? (member params '(if in => var)))
                     (parse (desugar s))]
    ;{var {[id = Expr] ...} in Expr} LamC 2 Case

    ;;> See note about (false? (member params '(if in => vars))) above. The following line also
    ;;>   does not check if the paramters of this lambda are one of the reserved symbols.
    ;{id ... => Expr} LamC {a 1 s f => {}} *needs to be made into a list
    [(list (? symbol? a) ... '=> b) #:when (and (false? (member a '(if in => var))) (unique? (cast a (Listof Symbol))))
                                    (LamC (cast a (Listof Symbol)) (parse b))]

    ;;> You should handle function application on reals in interp instead of parse since it deals with checking values
    ;;>   See section 5.2 of the assignment
    ;;> Also see above match statements about the (member f ('if in => var)) check
    [(list f a ...) #:when (and (false? (member f '(if in => var))) (not (real? f)))
                    (AppC (parse f) (for/list ([x (cast a (Listof Sexp))]) (parse x)))] ;{Expr Expr ...} AppC

    [else (error 'parse "JILI Invalid Syntax ~v" s)]))


;takes in a value input and returns a string
(define (serialize [output : Value]) : String
  (match output
    [(NumV n) (~v n)]
    [(BoolV b) (if b "true" "false")]
    ;;> Since BoolOpV is a PrimOpV, the serialize should be
    ;;>   "#<primop>"
    [(BoolOpV o) (~v o)]
    [(StrV s) (~v s)]
    [(CloV a b e) "#<procedure>"]
    [(PrimOpV o) "#<primop>"]
    ;;> Since ErrorV is a PrimOpV, the serialize should be
    ;;>   "#<primop>"
    ;;>   Also, note that when a user-defined error actually is raised,
    ;;>   you must include the string "user-error"
    [(ErrorV v) (error "JILI error:" v)]))

; define lookup, takes a symbol and environment and looks for the binding in the environment
(define (lookup [for : Symbol] [env : Env]) : Value ; helper function for interp - using for environments
  (cond
    [(empty? (Env-b env)) (error 'lookup "JILI Name not found")]
    [else (cond
            [(symbol=? for (Bind-s (first (Env-b env)))) (Bind-v (first (Env-b env)))]
            [else (lookup for (Env (rest (Env-b env))))])]))

; define newBind, binds list of symbols to list of values in new environment
(define (newBind [sym : (Listof Symbol)] [to : (Listof Value)]) : Env
  (cond
    ;;> Take a look at the definition of map. This function will be more clean than for/list:
    [(equal? (length sym) (length to)) (Env (for/list: : (Listof Bind) ([s sym]
                                                                        [val to])
                                              (Bind s val)))]
    [else (error 'interp "JILI Mismatching number of arguments")]))

;takes a Symbol and returns a function which takes two Reals and returns a Real
(define (apply-primitive [primop : PrimOpV]) : (-> Real Real Real)
  (match primop
    [(PrimOpV '+) +]
    [(PrimOpV '*) *]
    [(PrimOpV '-) -]
    [(PrimOpV '/) /]))

;define desugars the var form into the => form
(define (desugar [s : Sexp]) : Sexp
  (match s
    [(list 'var
           (list (list (? symbol? params) '= expr) ...)
           ;;> These casts should include a comment describing why they are safe to perform
           'in body) (cons (append (cast params (Listof Sexp)) (list '=> body)) (cast expr (Listof Sexp)))]))

;define unique?, takes a list of symbol and checks if unique
(define (unique? [a : (Listof Symbol)]) : Boolean
  (match a
    ['() #t]
    ;;> Convention is to name the parts of the cons "f" and "r" for first and rest instead of "a" and "b"
    [(cons a b) (if (false? (member a b)) (unique? b) #f)]))


; top-interp
(check-equal? (top-interp "hi") "\"hi\"")

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax"))
           (lambda () (top-interp '{a a => 3})))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax"))
           (lambda () (top-interp '{/ 1 {- 3 3}})))

; interp
(define test-env (Env (list (Bind 'a (StrV "hello")))))
(check-equal? (interp (IdC 'a) test-env) (StrV "hello"))
(check-equal? (interp (StrC "hello") top-env) (StrV "hello"))
(check-equal? (interp (NumC 1) top-env) (NumV 1))
(check-equal? (interp (IdC 'true) top-env) (BoolV true))
(check-equal? (interp (AppC (IdC '+) (list (NumC 1) (NumC 2))) top-env) (NumV 3))
(check-equal? (interp (AppC (LamC (list 'x) (AppC (IdC '*) (list (IdC 'x) (NumC 2)))) (list (NumC 1))) top-env)
              (NumV 2))
(check-equal? (interp (AppC (IdC '<=) (list (NumC 1) (NumC 2))) top-env) (BoolV true))
(check-equal? (interp (AppC (IdC 'equal?) (list (StrC "hello") (StrC "hello"))) top-env) (BoolV true))
(check-equal? (interp (AppC (IdC 'equal?) (list (LamC '(a) (NumC 1)) (StrC "hello"))) top-env) (BoolV false))
(check-equal? (interp (AppC (IdC 'equal?) (list (LamC '(a) (NumC 1)) (IdC '+))) top-env) (BoolV false))
(check-equal? (interp (AppC (IdC 'equal?) (list (StrC "hello") (LamC '(a) (NumC 1)))) top-env) (BoolV false))
(check-equal? (interp (AppC (IdC 'equal?) (list (IdC '/) (LamC '(a) (NumC 1)))) top-env) (BoolV false))
(check-equal? (interp (AppC (IdC 'equal?) (list (IdC '-) (IdC '/))) top-env) (BoolV false))
(check-equal? (interp (AppC (IdC 'equal?) (list (LamC '(a) (NumC 1)) (LamC '(a) (NumC 1)))) top-env) (BoolV false))
(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (StrC "ur") (StrC "mom")))
                           (AppC (IdC '-) (list (NumC 5) (NumC 2)))
                           (AppC (IdC '/) (list (NumC 4) (NumC 2)))) top-env) (NumV 2))
(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (StrC "mom") (StrC "mom")))
                           (AppC (IdC '-) (list (NumC 5) (NumC 2)))
                           (AppC (IdC '/) (list (NumC 3) (NumC 2)))) top-env) (NumV 3))
(check-equal? (interp (AppC (IdC 'error) (list (NumC 1))) top-env) (ErrorV (NumV 1)))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax"))
           (lambda () (top-interp '{+ + +})))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax"))
           (lambda () (top-interp '{<= <= <=})))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax"))
           (lambda () (top-interp '{if (+ 4 3) 1 2})))

; parse
(check-equal? (parse '{+ 1 2}) (AppC (IdC '+) (list (NumC 1) (NumC 2))))

(check-equal? (parse '{* {+ 1 2} 3}) (AppC (IdC '*) (list (AppC (IdC '+) (list (NumC 1) (NumC 2))) (NumC 3))))

(check-equal? (parse '{- 4 1}) (AppC (IdC '-) (list (NumC 4) (NumC 1))))

(check-equal? (parse '{/ 4 2}) (AppC (IdC '/) (list (NumC 4) (NumC 2))))

(check-equal? (parse '{+ {f {h x}} {i 9}}) (AppC (IdC '+)
                                                 (list (AppC (IdC 'f) (list (AppC (IdC 'h) (list (IdC 'x)))))
                                                       (AppC (IdC 'i) (list (NumC 9))))))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax"))
           (lambda () (parse '{})))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax"))
           (lambda () (parse '{})))

(check-equal? (parse '{f 1 2 3}) (AppC (IdC 'f) (list (NumC 1) (NumC 2) (NumC 3))))

(check-equal? (parse '{test-func x y}) (AppC (IdC 'test-func) (list (IdC 'x) (IdC 'y))))

(check-equal? (parse '{test-no-args}) (AppC (IdC 'test-no-args) '()))

(check-equal? (parse '{a => {+ a 1}}) (LamC (list 'a) (AppC (IdC '+) (list (IdC 'a) (NumC 1)))))

(check-equal? (parse '{if a b c}) (IfC (IdC 'a) (IdC 'b) (IdC 'c)))
(check-equal? (parse 1) (NumC 1))
(check-equal? (parse "s") (StrC "s"))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}})
              (AppC (LamC '(z y)
                          (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))



; serialize
(check-equal? (serialize (NumV 3)) "3")  ;NumV
(check-equal? (serialize (BoolV false)) "false")   ;BoolV
(check-equal? (serialize (BoolV true)) "true")   ;BoolV
(check-equal? (serialize (BoolOpV 'true)) "'true")  ; BoolOpV
(check-equal? (serialize (StrV "test")) "\"test\"") ;StrV
(check-equal? (serialize (CloV (list 'b 'c) (IdC 'a) test-env)) "#<procedure>") ;CloV
(check-equal? (serialize (PrimOpV '+)) "#<primop>")  ;PrimOpV
(check-exn (regexp (regexp-quote "JILI error: 'x"))
           (lambda () (serialize (ErrorV 'x))))

;newBind
(check-equal? (newBind (list 'a 'b 'c) (list (NumV 1) (NumV 2) (NumV 3)))
              (Env (list (Bind 'a (NumV 1))
                         (Bind 'b (NumV 2))
                         (Bind 'c (NumV 3)))))

(check-exn (regexp (regexp-quote "interp: JILI Mismatching number of arguments"))
           (lambda () (top-interp '((=> 9) 17))))

; desugar
(check-equal? (desugar '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}})
              '((z y => {+ z y})(+ 9 14) 98))

; lookup
(check-exn (regexp (regexp-quote "lookup: JILI Name not found"))
           (lambda () (interp (IdC 'x) top-env)))
