#lang typed/racket

(require typed/rackunit)


(define-type ExperC (U NumC IdC AppC IfC Symbol LamC StringC RecC))
(define-type Value (U NumV BoolV CloV StringV PrimV))
(define-type Type (U NumT StringT BoolT FuncT))

;;> would be nice to have comment desciptions above the type definitions to clean up your code
(struct BoolT ()
  #:transparent)
(struct NumT ()
  #:transparent)
(struct StringT ()
  #:transparent)
(struct FuncT ([args : (Listof Type)] [ret : Type])
  #:transparent)

(struct StringC ([string : String])
  #:transparent)
(struct IdC ([name : Symbol])
  #:transparent)
(struct NumC ([n : Real])
  #:transparent)

(struct AppC ([body : ExperC][argc : (Listof ExperC)])
  #:transparent)
(struct IfC ([argc : ExperC] [t : ExperC] [f : ExperC])
  #:transparent)
(struct LamC ([arg : (Listof Symbol)] [argtypes : (Listof Type)] [body : ExperC])
  #:transparent)
(struct RecC ([name : Symbol] [arg : (Listof Symbol)] [argtypes : (Listof Type)]
                              [retType : Type] [body : ExperC] [in : ExperC])
  #:transparent)

(struct PrimV ([s : Symbol])
  #:transparent)
(struct CloV ([arg : (Listof Symbol)] [body : ExperC] [env : Env])
  #:transparent)
(struct StringV ([string : String])
  #:transparent)
(struct BoolV ([bool : Boolean])
  #:transparent)

(struct NumV ([n : Real])
  #:transparent)

(struct Binding ([name : Symbol] [boxval : (Boxof Value)])
  #:transparent)

(struct TyBinding ([name : Symbol] [type : Type])
  #:transparent)

(struct TEnv ([list : (Listof TyBinding)])
  #:transparent)

(struct Env ([list : (Listof Binding)])
  #:transparent)

;top-level environment that holds boolean
(define boxv (inst box Value))
(define top-level (Env (list
                        (Binding 'true (boxv (BoolV #t)))
                        (Binding 'false (boxv (BoolV #f)))
                        (Binding '+ (boxv (PrimV '+)))
                        (Binding '- (boxv (PrimV '-)))
                        (Binding '/ (boxv (PrimV '/)))
                        (Binding '* (boxv (PrimV '*)))
                        (Binding '<= (boxv (PrimV '<=)))
                        (Binding 'num-eq? (boxv (PrimV 'num-eq?)))
                        (Binding 'str-eq? (boxv (PrimV 'str-eq?)))
                        (Binding 'substring (boxv (PrimV 'substring)))
                        (Binding 'error (boxv (PrimV 'error))))))

;;> add description for this
(define empty-env (Env '()))

;;> add description for this
(define base-tenv (TEnv (list
                         (TyBinding 'true (BoolT))
                         (TyBinding 'false (BoolT))
                         (TyBinding '* (FuncT (list (NumT) (NumT)) (NumT)))
                         (TyBinding '+ (FuncT (list (NumT) (NumT)) (NumT)))
                         (TyBinding '- (FuncT (list (NumT) (NumT)) (NumT)))
                         (TyBinding '/ (FuncT (list (NumT) (NumT)) (NumT)))
                         (TyBinding '<= (FuncT (list (NumT) (NumT)) (BoolT)))
                         (TyBinding 'num-eq? (FuncT (list (NumT) (NumT)) (BoolT)))
                         (TyBinding 'str-eq? (FuncT (list (StringT) (StringT)) (BoolT)))
                         (TyBinding 'substring (FuncT (list (StringT) (NumT) (NumT)) (StringT)))
                         (TyBinding 'error (FuncT (list (StringT)) (StringT))))))

;parses and run JYSS program
(: top-interp (Sexp -> String))
(define (top-interp s)
  (define ast (parse s))
  (type-check ast base-tenv)
  (serialize (interp ast top-level)))

;Converts value types to strings
(define (serialize [val : Value]) : String
  (match val
    [(NumV val) (~v val)]
    [(BoolV bool) (cond
                    [bool "true"]
                    [else "false"])]
    [(CloV arg body env) "#<procedure>"]
    [(StringV string) (~v string)]
    [(PrimV s) "#<primop>"]))


;checks if s has reserved keywords
(define (reserved? [s : Sexp ]) : Boolean
 (match s
   ['go #t]
   ['proc #t]
   ['vars: #t]
   ['body: #t]
   ['if #t]
   ['fn #t]
   [': #t]
   ['in #t]
   ['rec #t]
   ['= #t]
   ['-> #t]
   [else #f]))


;parser for ExperC
;parses a S-expression and returns ExperC
(define (parse [s : Sexp]) : ExperC
   (match s
     [(? real? n) (NumC n)]
     [(? string? s) (StringC s)]
     [(list 'if test then else) (IfC (parse test) (parse then) (parse else))]
     [(? symbol? id) (cond
                       [(not (reserved? id)) (IdC id)]
                       [else (error 'parse "JYSS: invalid variable name: ~e" id)])]
     ;[(list 'proc (list (? symbol? vars) ...) 'go expr)
     [(list 'proc (list (list (? symbol? vars) ': ty1) ...) 'go expr)
      (cond
        [(not (equal? (length (remove-duplicates vars)) (length vars)))
;;> Error messages should display the incorrect program text; this makes them useful.
         (error 'parse "JYSS: function parameters cannot have same name")]
        ;(extend-type-env (Binding vars (parse-type ty1)))
        [else (LamC (cast vars (Listof Symbol)) (map parse-type (cast ty1 (Listof Sexp))) (parse expr))])]
     [(list 'vars: bindings ... 'body: expr)
      (match bindings
        [(list (list (? symbol? vars) ': ty '= exprs) ...)
         (cond
           [(not (equal? (length (remove-duplicates vars)) (length vars)))
;;> Error messages should display the incorrect program text; this makes them useful.
            (error 'parse "JYSS: function parameters cannot have same name")]
           [else (cond
                   [(not (valid-var? (cast vars (Listof Sexp))))
;;> Error messages should display the incorrect program text; this makes them useful.
                    (error 'parse "JYSS: parameters must be symbols")]
                   [else (AppC (LamC (cast vars (Listof Symbol))
                                     (map parse-type (cast ty (Listof Sexp))) (parse expr))
                               (map parse (cast exprs (Listof Sexp))))])])]
        [other (error 'parse "JYSS: Not a valid 'vars' form: ~e" other)])]
     ;{rec: [id = {proc {[id : ty] ...} : ty go expr}] in expr}
     [(list 'rec: bindings 'in in-body)
      (match bindings
        [(list (? symbol? id) '= (list 'proc (list (list (? symbol? vars) ': ty1) ...)
                                                ': ty2 'go rec-body))
         (RecC id (cast vars (Listof Symbol)) (map parse-type (cast ty1 (Listof Sexp)))
            (parse-type ty2) (parse rec-body) (parse in-body))]
        ;[other (error 'parse "JYSS: Not a valid 'rec' form: ~e" other)]
;;> This line contains nothing but close parens:
        )]
     [(list func vars ...) (cond
                             [(equal? func 'if) (error 'parse "JYSS: Incorrect 'if' form")]

                              [(not (valid-var? (cast vars (Listof Sexp))))
                               (error 'parse "JYSS: parameters must be symbols")]
                              [else (AppC (parse func) (map parse (cast vars (Listof Sexp))))])]
     [other (error 'parse "JYSS: invalid input: ~e" other)]))



;parses a S-expression and returns a Type
(define (parse-type [s : Sexp]) : Type
  (match s
    ['num (NumT)]
    ['str (StringT)]
    ['bool (BoolT)]
    [(list s ... '-> t) (FuncT (map parse-type (cast s (Listof Sexp))) (parse-type t))]
    [other (error 'parse-type "JYSS: Invalid Type: ~e" other)]))

;Checks if the given AST is consistent between the defined and given types. Returns the type of the given ExperC.
(define (type-check [e : ExperC] [ty-env : TEnv]) : Type
  (match e
    [(NumC n) (NumT)]
    [(StringC s) (StringT)]
    [(IdC c) (Tyenv-lookup c ty-env)]
    [(IfC test t f)
     (match (type-check test ty-env)
       [(BoolT)
        (define then (type-check t ty-env))
        (define else (type-check f ty-env))
        (cond
          [(equal? then else) then]
          [else
           (error 'type-check "JYSS: if expression 'then' and 'else' branches not of same type: ~e ~e" then else)])]
       [other (error 'type-check "JYSS: if expression's 'test' must return a boolean value: ~e" other)])]
    [(AppC f args)
     (define funtype (type-check f ty-env))
     (define argstype (arglist-type args ty-env))
     (cond
       [(not (FuncT? funtype)) (error 'type-check "JYSS: Not a function type: ~e : ~e" f funtype)]
       [(not (equal? (FuncT-args funtype) argstype))
        (error 'type-check "JYSS: Argument types do not match those of function parameters. Expected and Given: ~e ~e"
               (FuncT-args funtype) argstype)]
       [else (FuncT-ret funtype)])]
    [(LamC args argtypes body)
     (define new-tyenv (extend-tyenv args argtypes ty-env))
       (FuncT argtypes (type-check body new-tyenv))]
    [(RecC name args argtypes rettype rec-body main-body)
     (define new-tyenv (extend-tyenv args argtypes (extend-tyenv (list name) (list (FuncT argtypes rettype)) ty-env)))
     (cond
       [(not (equal? rettype (type-check rec-body new-tyenv)))
        (error 'type-check "JYSS: Recursive function incorrect return type. Given and expected: ~e ~e"
               rettype (type-check rec-body new-tyenv))]
       [else (type-check main-body new-tyenv)])
;;> This line contains nothing but close parens:
     ]))

;type-checks a list of ExperC's
(define (arglist-type [args : (Listof ExperC)] [ty-env : TEnv]) : (Listof Type)
  (match args
    ['() '()]
    [(cons f r) (cons (type-check f ty-env) (arglist-type r ty-env))]))



;function to iterate the list of symbols and determine if each is a reserved symbol or not
(define (valid-var? [v : (Listof Sexp)]): Boolean
  (match v
    ['() #t]
    [(cons f r) (cond
                  [(reserved? f) #f]
                  [else (valid-var? r)])]))


;takes in a symbol and returns its corresponding value within the environment
(define (env-lookup [for : Symbol] [env : Env]) : (Boxof Value)
  (match env
    [(Env e)
     (match e
       ['() (error 'env-lookup "JYSS variable name not found")]
       [(cons f r) (cond
            [(symbol=? for (Binding-name f))
             (Binding-boxval f)]
            [else (env-lookup for (Env r))])])]))

;takes in a symbol and returns its corresponding type within the environment
(define (Tyenv-lookup [for : Symbol] [tyenv : TEnv]) : Type
  (match tyenv
    [(TEnv e)
     (match e
       ['() (error 'Tyenv-lookup "JYSS: Symbol does not have an assigned type in the environment: ~e" for)]
       [(cons f r) (cond
            [(symbol=? for (TyBinding-name f))
             (TyBinding-type f)]
            [else (Tyenv-lookup for (TEnv r))])])]))


;add a (Symbol -> Boxof Value) binding to the current environment
(define (extend-env [sym : (Listof Symbol)] [arg : (Listof (Boxof Value))] [env : Env]) : Env
  (match sym
    ['() env]
    [(cons f r)
     (match env
       [(Env e) (extend-env r (rest arg) (Env (append (list (Binding f (first arg))) e)))])]))

;add a (Symbol -> Type) binding to the current type environment
(define (extend-tyenv [sym : (Listof Symbol)] [ty : (Listof Type)] [tenv : TEnv]) : TEnv
  (match sym
    ['() tenv]
    [(cons f r)
     (match tenv
       [(TEnv e) (extend-tyenv r (rest ty) (TEnv (append (list (TyBinding f (first ty))) e)))])]))


;checks if Value is a numV type
(define (numV-check [val : Value]) : NumV
  (match val
    [(NumV v) (NumV v)]
    [other (error 'numV-check "JYSS value is not a numV")]))

;interprets all arguments in an argument list
(define (interp-arglist [args : (Listof ExperC)] [env : Env]) : (Listof (Boxof Value))
  (match args
    ['() '()]
    [(cons f r) (cons (boxv (interp f env)) (interp-arglist r env))]))


;interprets the given expression, using the list of funs to resolve
;applications and returns a real
(define (interp [e : ExperC][env : Env]) : Value
  (match e
    [(NumC n) (NumV n)]
    [(IdC name) (unbox (env-lookup name env))]
    [(LamC param paramtypes body) (CloV param body env)]
    [(StringC str) (StringV str)]
    [(AppC body arg)
     (match (interp body env)
       [(PrimV sym)
        (cond
          [(equal? (length arg) 1)
           (match sym
             ['error (error 'error "JYSS: user-error: ~e" (serialize (interp (first arg) env)))])]
          [(equal? (length arg) 2)
           (match sym
           ;;> a lot of this logic for handling PrimV can be abstracted out to its own function(s) to clean up interp
             ['+ (NumV (+ (NumV-n (numV-check (interp (first arg) env)))
                          (NumV-n (numV-check (interp(second arg) env)))))]
             ['- (NumV (- (NumV-n (numV-check (interp (first arg) env)))
                          (NumV-n (numV-check (interp(second arg) env)))))]
             ['* (NumV (* (NumV-n (numV-check (interp (first arg) env)))
                          (NumV-n (numV-check (interp(second arg) env)))))]
             ['/ (cond
                   [(equal? (NumV-n (numV-check (interp (second arg) env))) 0)
                    (error 'interp "JYSS divided by 0 error")]
                   [else (NumV (/ (NumV-n (numV-check (interp (first arg) env)))
                                  (NumV-n (numV-check (interp(second arg) env)))))])]
             ['<= (BoolV (<= (NumV-n (numV-check (interp (first arg) env)))
                             (NumV-n (numV-check (interp (second arg) env)))))]
             ['str-eq? (match (map unbox (interp-arglist arg env))
                        [(list (? StringV? arg1) (? StringV? arg2))
                         (BoolV (equal? (StringV-string arg1) (StringV-string arg2)))]
                        [other (BoolV #false)])]
             ['num-eq? (match (map unbox (interp-arglist arg env))
                        [(list (? NumV? arg1) (? NumV? arg2))
                         (BoolV (equal? (NumV-n arg1) (NumV-n arg2)))]
                        [other (BoolV #false)])])]
          [(equal? (length arg) 3)
           (match sym
             ['substring (match (map unbox (interp-arglist arg env))
                           [(list (? StringV? arg1) (? NumV? arg2) (? NumV? arg3))
                            (cond
                              [(and
                                (exact-nonnegative-integer? (NumV-n arg2)) (exact-nonnegative-integer? (NumV-n arg3)))
                               (StringV (substring (StringV-string arg1) (NumV-n arg2) (NumV-n arg3)))]
                              [else
                               (error 'interp "JYSS: invalid substring arguments. Given: ~e ~e ~e" arg1 arg2 arg3)])])]
             [other (error 'interp "JYSS: invalid primop form: ~e" sym)])]
          [else (error 'interp "JYSS: invalid primop form: ~e" sym)])]

       [(CloV param body clenv)
        (define argval (interp-arglist arg env))
        (define new-env (extend-env param argval clenv))
        (interp body new-env)])]

    [(IfC exp t f)
     (match (interp exp env)
       [(? BoolV? result) (cond
                            [(BoolV-bool result) (interp t env)]
                            [else (interp f env)])])]
    [(RecC name arg argtypes retType body in)
     (define new-env (extend-env (list name) (list (boxv (NumV 0))) env))
     (define closure (CloV arg body new-env))
     (set-box! (env-lookup name new-env) closure)
     (interp in new-env)]))


;Test cases
(check-equal? (top-interp '{substring "abcd" 0 2}) "\"ab\"")
(check-equal? (interp (AppC (IdC 'substring) (list (StringC "abcd") (NumC 0) (NumC 2))) top-level) (StringV "ab"))
(check-exn (regexp (regexp-quote "JYSS: invalid substring arguments. Given: "))
           (lambda () (top-interp '(substring "abc" 1.1 2))))

(check-exn (regexp (regexp-quote "JYSS: parameters must be symbols"))
           (lambda () (parse '{+ if 4})))
(check-exn (regexp (regexp-quote "JYSS: parameters must be symbols"))
           (lambda () (parse '{vars: [if : num = 2] body: {+ 3 4}})))

(check-exn (regexp (regexp-quote "JYSS: if expression 'then' and 'else' branches not of same type:"))
           (lambda () (top-interp '{vars: body: {if true 5 "abc"}})))

(check-equal? (top-interp '{rec: [square-helper =
       {proc {[n : num]} : num go
         {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}]
 in
 {vars: [square : {num -> num}  =
         {proc {[n : num]} go {square-helper {- {* 2 n} 1}}}]
  body:
  {square 13}}}) "169")

#;(check-exn (regexp (regexp-quote "body return type not correct"))
           (lambda ()(top-interp '{rec: [square-helper =
       {proc {[n : num]} : num go
         {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}]
 in
 {vars: [square : {num -> num}  =
         {proc {[n : num]} go {square-helper {- {* 2 n} 1}}}]
  body:
  {square 13}}})))

(check-equal? (type-check (parse '(if true 0 1)) base-tenv) (NumT))
(check-equal? (type-check (IfC (IdC 'true) (NumC 0) (NumC 1)) base-tenv) (NumT))

(check-equal? (type-check (parse 3) base-tenv) (NumT))
(check-equal? (type-check (parse "yo") base-tenv) (StringT))
(check-equal? (type-check (parse 'true) base-tenv) (BoolT))
(check-equal? (type-check (parse '*) base-tenv) (FuncT (list (NumT) (NumT)) (NumT)))
(check-exn (regexp (regexp-quote "JYSS: Symbol does not have an assigned type in the environment: "))
           (lambda () (type-check (parse 'alsdkjfh) base-tenv)))

(check-equal? (parse-type 'num) (NumT))
(check-equal? (parse-type 'str) (StringT))
(check-equal? (parse-type 'bool) (BoolT))
(check-equal? (parse-type '{num str bool -> num}) (FuncT (list (NumT) (StringT) (BoolT)) (NumT)))
(check-equal? (parse-type '{num -> (str -> bool)}) (FuncT (list (NumT)) (FuncT (list (StringT)) (BoolT))))
(check-equal? (parse-type '{num (str str -> bool) bool -> num})
              (FuncT (list (NumT) (FuncT (list (StringT) (StringT)) (BoolT)) (BoolT)) (NumT)))
(check-exn (regexp (regexp-quote "JYSS: Invalid Type: ")) (lambda () (parse-type '{aye what -> yuh})))

(check-exn (regexp (regexp-quote "JYSS: invalid variable name: "))
           (lambda () (parse '(if 0 proc 1))))

(check-exn (regexp (regexp-quote "JYSS: user-error: "))
                  (lambda () (top-interp '(error "1234"))))



(check-exn (regexp
            (regexp-quote "JYSS: Argument types do not match those of function parameters. Expected and Given: "))
                  (lambda () (top-interp '(+ 4 (+ "1234")))))


(check-equal? (reserved? 'if) #true)
(check-equal? (reserved? 'fn) #true)
(check-equal? (reserved? 'vars:) #true)
(check-equal? (reserved? 'body:) #true)
(check-equal? (reserved? 'proc) #true)
(check-equal? (reserved? 'go) #true)
(check-equal? (reserved? ':) #true)
(check-equal? (reserved? 'in) #true)
(check-equal? (reserved? 'rec) #true)
(check-equal? (reserved? '=) #true)
(check-equal? (reserved? '->) #true)

;(top-interp '{{proc {} go 9} 17})

(check-exn (regexp (regexp-quote "JYSS: Not a function type:"))
           (lambda () (type-check (AppC (IdC 'true) (list (NumC 5))) base-tenv)))

(check-exn (regexp (regexp-quote "JYSS: Recursive function incorrect return type. Given and expected: "))
           (lambda () (type-check (parse '(rec: (a = (proc ((c : num)) : num go "abc")) in 13)) base-tenv)))

#;(check-exn (regexp (regexp-quote "JYSS: argList and paramList not of equal length"))
           (lambda () (top-interp '{{proc {} go 9} 5} )))


#;(check-exn (regexp (regexp-quote "JYSS: Not a function type: "))
                                 (lambda ()(top-interp '{3 2 1})))

(check-equal? (top-interp '{vars:
  [z : num = {+ 9 14}]
  [y : num = 98]
 body:
  {+ z y}}) "121")




(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (NumV 4)) "4")
(check-equal? (serialize (StringV "hi")) "\"hi\"")


(check-equal? (interp (IdC 'x) (Env (list (Binding 'x (boxv (NumV 6)))))) (NumV 6))


(check-equal? (top-interp '{{proc {[x : num]} go {+ x 2}} 3})
              "5")

(check-exn (regexp (regexp-quote "JYSS: invalid primop form:"))
           (lambda () (interp (AppC (IdC '+) (list (NumC 5) (NumC 2) (NumC 3))) top-level)))

(check-exn (regexp (regexp-quote "JYSS: Not a valid 'vars' form: '((z = (proc () go 3)) (z = 9))"))
           (lambda () (top-interp '(vars: (z = (proc () go 3)) (z = 9) body: (z)))))

(check-exn (regexp (regexp-quote "JYSS: invalid primop form:"))
           (lambda () (interp (AppC (IdC '+) (list (NumC 5) (NumC 2) (NumC 3) (NumC 3))) top-level)))

(check-equal? (interp (IfC (AppC (IdC 'num-eq?) (list (NumC 2) (NumC 2))) (NumC 1) (NumC 0)) top-level) (NumV 1))
(check-equal? (interp (IfC (AppC (IdC 'str-eq?) (list (NumC 2) (NumC 2))) (NumC 1) (NumC 0)) top-level) (NumV 0))
(check-equal? (interp (IfC (AppC (IdC 'str-eq?) (list (StringC "456") (StringC "123")))
                           (NumC 1) (NumC 0)) top-level) (NumV 0))
(check-equal? (interp (IfC (AppC (IdC 'num-eq?) (list (StringC "456") (StringC "123")))
                           (NumC 1) (NumC 0)) top-level) (NumV 0))

(check-equal? (parse '{proc {[z : num] [y : num]} go {+ z y}})
              (LamC '(z y) (list (NumT) (NumT)) (AppC (IdC '+) (list (IdC 'z) (IdC 'y)))))

(check-equal? (parse '{vars: [z : num = {+ 9 14}] [y : num = 98] body: {+ z y}})
               (AppC (LamC '(z y) (list (NumT) (NumT)) (AppC (IdC '+) (list (IdC 'z)(IdC 'y))))
                     (list (AppC (IdC '+) (list (NumC 9)(NumC 14))) (NumC 98))))

(check-exn (regexp (regexp-quote "JYSS: invalid input: ")) (lambda () (parse '{})))

(check-equal? (parse '{vars: [z : num = {+ 9 14}] [y : num = 98] body: {+ z y}})

              (parse '{{proc {[z : num ] [y : num]} go {+ z y}} {+ 9 14} 98}))

(check-exn (regexp (regexp-quote "JYSS variable name not found" ))
           (lambda () (env-lookup 'a (Env (list (Binding 'b (boxv (NumV 3))))))))


(check-equal? (interp (AppC (IdC '+) (list (AppC (IdC '+) (list (NumC 3)(NumC 4)))
                              (AppC (IdC '+) (list (NumC 3) (NumC 3))))) top-level) (NumV 13))

(check-equal? (serialize (CloV (list 'a) (NumC 5) (Env (list (Binding 'x (boxv (NumV 4))))))) "#<procedure>")
(check-equal? (serialize (BoolV true)) "true")
(check-equal? (reserved? 'asdf) #f)

(check-equal? (interp (AppC (IdC '*) (list (NumC 3)(NumC 4))) top-level) (NumV 12))
(check-equal? (interp (AppC (IdC '/) (list (NumC 4)(NumC 4))) top-level) (NumV 1))
(check-equal? (interp (AppC (IdC '-) (list (NumC 5)(NumC 0))) top-level) (NumV 5))
(check-exn (regexp (regexp-quote "JYSS divided by 0 error"))
             (lambda () (interp (AppC (IdC '/) (list (NumC 0)(NumC 0))) top-level)))

(check-exn (regexp (regexp-quote "JYSS value is not a numV")) (lambda () (numV-check (BoolV #true))))

(check-exn (regexp (regexp-quote "JYSS: function parameters cannot have same name"))
           (lambda () (top-interp '{{proc {[x : num] [x : num]} go {str-eq? "yo" x}} "yo"})))
(check-exn (regexp (regexp-quote "JYSS: function parameters cannot have same name"))
           (lambda () (top-interp '{vars:
                                    [z : num = {+ 9 14}]
                                    [z : num = 98]
                                    body:
                                    {+ z 1}})))

(check-equal? (interp (AppC (IdC '<=) (list (NumC 5) (NumC 3))) top-level) (BoolV #false))
(check-equal? (interp (AppC (IdC '<=) (list (NumC 1) (NumC 3))) top-level) (BoolV #true))
(check-equal? (interp (AppC (IdC 'num-eq?) (list (NumC 5) (NumC 5))) top-level) (BoolV #true))
;(check-equal? (interp (AppC (IdC 'equal (list (IdC 'true) (IdC 'false))) top-level) (BoolV #false))
;(check-equal? (interp (AppC (IdC 'equal?) (list (IdC '+) (IdC '+))) top-level) (BoolV #false))
(check-equal? (interp (AppC (IdC 'str-eq?) (list (StringC "5") (StringC "5"))) top-level) (BoolV #true))
(check-equal? (top-interp '{{proc {[x : str]} go {str-eq? "yo" x}} "yo"}) "true")


(check-exn  (regexp (regexp-quote "JYSS: Incorrect 'if' form"))
            (lambda () (top-interp '{{proc {[x : num]} go {if {+ 2 1} true}} 3})))
(check-exn  (regexp (regexp-quote "JYSS: if expression's 'test' must return a boolean value:"))
            (lambda () (top-interp '{if {+ 4 3} 7 8})))

;(check-equal? (top-interp '{{proc go {if {equal? 2 1} true false}}}) "#f")
(check-equal? (top-interp '{{proc {[x : num]} go {if {num-eq? x 5} true false}} 5}) "true")
(check-equal? (top-interp '{{proc {[x : num]} go {if {num-eq? x 5} true false}} 3}) "false")


