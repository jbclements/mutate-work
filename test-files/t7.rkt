#lang typed/racket

(require typed/rackunit)



; Full project implemented (Test cases at very bottom)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Define tstruct with Transparent tag
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Data Defintions


; ExprC
(define-type ExprC (U numC IdC StringC AppC lamC ifC recC))
(tstruct numC ([n : Real]))
(tstruct IdC ([s : Symbol]))
(tstruct StringC ([str : String]))
(tstruct AppC ([fun : ExprC] [args : (Listof ExprC)]))
(tstruct lamC ([arg : (Listof Symbol)] [argT : (Listof Ty)] [body : ExprC]))
(tstruct ifC ([test : ExprC] [then : ExprC] [else : ExprC]))
(tstruct recC ([fun : Symbol] [args : (Listof Symbol)] [argT : (Listof Ty)]
               [retT : Ty] [b : ExprC] [u : ExprC]))


; Value
(define-type Value (U Real Boolean String closV primV))
(tstruct closV ([arg : (Listof Symbol)] [body : ExprC] [env : Env]))
(tstruct primV ([op : Symbol]))


; For Normal Environments
(tstruct Binding ([name : Symbol] [val : (Boxof Value)]))
(define boxV (inst box Value))
(tstruct Env ([bindings : (Listof Binding)]))
(define empty-Env (Env '()))
(define top-env (Env (list (Binding 'true (boxV #true))
                           (Binding 'false (boxV #false))
                           (Binding '+ (boxV (primV '+)))
                           (Binding '- (boxV (primV '-)))
                           (Binding '* (boxV (primV '*)))
                           (Binding '/ (boxV (primV '/)))
                           (Binding '<= (boxV (primV '<=)))
                           (Binding 'num-eq? (boxV (primV 'num-eq?)))
                           (Binding 'str-eq? (boxV (primV 'str-eq?)))
                           (Binding 'substring (boxV (primV 'substring))))))


; Types
(define-type Ty (U numT boolT strT funT))
(tstruct numT ())
(tstruct boolT ())
(tstruct strT ())
(tstruct funT ([argT : (Listof Ty)] [retT : Ty]))


; For Type Environments
(tstruct TBinding ([name : Symbol] [type : Ty]))
(tstruct TEnv ([TBindings : (Listof TBinding)]))
(define base-tenv (TEnv (list (TBinding 'true (boolT)) (TBinding 'false (boolT))
                             (TBinding '+ (funT (list (numT) (numT)) (numT)))
                             (TBinding '- (funT (list (numT) (numT)) (numT)))
                             (TBinding '* (funT (list (numT) (numT)) (numT)))
                             (TBinding '/ (funT (list (numT) (numT)) (numT)))
                             (TBinding '<= (funT (list (numT) (numT)) (boolT)))
                             (TBinding 'num-eq? (funT (list (numT) (numT)) (boolT)))
                             (TBinding 'str-eq? (funT (list (strT) (strT)) (boolT)))
                             (TBinding 'substring (funT (list (strT) (numT) (numT)) (strT))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; TOP-INTERP


; Combines parsing, type-checking, interpretation, and serialization
(define (top-interp [s : Sexp]) : String
  (define parsed (parse s))
  (type-check parsed base-tenv)
  (serialize (interp parsed top-env)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; PARSER FUNCTIONS

;;> I suggest adding comments above each match condition to indicate which ExprC the Sexp is (potentially) being parsed into for readability
; Parses s-expressions
(define (parse [s : Sexp]) : ExprC
  (match s
    [(list 'rec: (list (? symbol? fname) '= (list 'proc (list args ...) ': retT 'go body)) 'in use)
     (cond
       [(is-reserved fname) (error 'parse "JYSS error: function name is reserved ~e" fname)]
       [else (define types (map parse-arg args))
             (define arg-names (map parse-arg-name args))
             (recC fname arg-names types (parse-type retT) (parse body) (parse use))])]
    [(list 'vars: args ... 'body: body) (parse (desugar s))]
    [(? real? num) (numC num)]
    [(? string? str) (StringC str)]
    [(list 'if rst ...) (match rst
                          [(list test then else) (ifC (parse test) (parse then) (parse else))]
                          [other (error 'parse "JYSS error: Incorrect format for if statement ~e" s)])]
    [(list 'proc (list args ...) 'go body)
     (define types (map parse-arg args))
     (define arg-names (map parse-arg-name args))
     (cond
       [(check-duplicates arg-names) (error 'parse "JYSS error: mulitple args with same name ~e" arg-names)]
       [(is-reserved-inList arg-names)
        (error 'parse "JYSS error: arg names can't be reserved keywords ~e" arg-names)]
       [else (lamC arg-names types (parse body))])]
    [(list sexps ...) (AppC (parse (first sexps)) (parseEach (rest sexps)))]
    [(? symbol? syb) (cond
                       [(is-reserved syb)
                        (error 'parse "JYSS error: variable name can't be reserved keyword ~e" syb)]
                       [else (IdC syb)])]
    [other (error 'parse "JYSS error: invalid expression given ~e" s)]))


; Translates from vars format to proc format
(define (desugar [s : Sexp]) : (Listof Sexp)
   (match s
     [(list 'vars: args ... 'body: body)
      (append (list (list 'proc (reformat (getArgNames (cast args (Listof Sexp)))
                                          (map parse-type-sexp (cast args (Listof Sexp)))) 'go body))
              (getArgValues (cast args (Listof Sexp))))]
     [other (error 'desugar "JYSS error: should never reach here ~e" s)]))


; Given a list of args and types return in list in format {[id : ty] ...}
(define (reformat [argNames : (Listof Sexp)] [types : (Listof Sexp)]) : (Listof Sexp)
  (match argNames
            ['() '()]
            [(cons f r) (append (list (list f ': (first types))) (reformat r (rest types)))]))


; Gets all argument names; input looks like "[z : num = {+ 9 14}] [y : num = 98]"
(define (getArgNames [s : (Listof Sexp)]) : (Listof Sexp)
  (match s
    ['() '()]
    [(cons f r) (match f
                    [(list argName ': type '= argValue) (cons argName (getArgNames r))]
                    [other (error 'getArgNames "JYSS error: wrong format given ~e" s)])]))


; Gets all argument values; input looks like "[z = {+ 9 14}] [y = 98]"
(define (getArgValues [s : (Listof Sexp)]) : (Listof Sexp)
  (match s
    ['() '()]
    [(cons f r) (match f
                    [(list argName ': type '= argValue) (cons argValue (getArgValues r))]
                    [other (error 'getArgNames "JYSS error: wrong format given ~e" s)])]))

; Get type out of Sexp, returns type in Sexp form
(define (parse-type-sexp [s : Sexp]) : Sexp
  (match s
    [(list (? symbol? s) ': type) type]
    [(list (? symbol? s) ': type '= expr) type]
    [other (error 'parse-arg-name "JYSS error: Wrong format given ~e" s)]))


; Get type out of Sexp, returns type in Ty form
(define (parse-arg [s : Sexp]) : Ty
  (match s
    [(list (? symbol? s) ': type) (parse-type type)]
    [(list (? symbol? s) ': type '= expr) (parse-type type)]
    [other (error 'parse-arg "JYSS error: Wrong format given ~e" s)]))


; Get arg name from given Sexp
(define (parse-arg-name [s : Sexp]) : Symbol
  (match s
    [(list (? symbol? s) ': type) s]
    [(list (? symbol? s) ': type '= expr) s]
    [other (error 'parse-arg-name "JYSS error: Wrong format given ~e" s)]))


; Given type in Sexp, returns actual Type
(define (parse-type [s : Sexp]) : Ty
  (match s
    ['num (numT)]
    ['bool (boolT)]
    ['str (strT)]
    [(list types ... '-> type) (funT (cast (map parse-type (cast types (Listof Sexp))) (Listof Ty)) (parse-type type))]
    [other (error 'parse-type "JYSS error: Type not supported ~e" s)]))


; Parses each argument
(define (parseEach [sexp : Sexp]) : (Listof ExprC)
  (match sexp
    ['() '()]
    [(cons f r) (cons (parse f) (parseEach r))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; TYPE CHECKING


; Typer-checker function
(define (type-check [e : ExprC] [tenv : TEnv]) : Ty
  (match e
    [(numC n) (numT)]
    [(IdC n) (TEnv-lookup tenv n)]
    [(StringC str) (strT)]
    [(AppC func args) (define funcTy (type-check func tenv))
                      (define argsTy (map type-check args (build-list (length args) (lambda (x) tenv))))
                      (cond
                        [(not (funT? funcTy)) (error 'type-check "JYSS error: not a function ~e" func)]
                        [(not (equal? (length argsTy) (length (funT-argT funcTy))))
                         (error 'type-check "JYSS error: wrong number of arguments provided ~e" e)]
                        [(not (equal? (funT-argT funcTy) argsTy))
                         (error 'type-check "JYSS error: app arg mismatch ~e" func)]
                        [else (funT-retT funcTy)])]
    [(lamC args argsTy body)
                      (define newTEnv (extend-TEnv args argsTy tenv))
                      (funT argsTy (type-check body newTEnv))]
    [(recC f a aT rT b u) (define extended-env (extend-TEnv (list f) (list (funT aT rT)) tenv))
                          (cond
                            [(not (equal? rT (type-check b (extend-TEnv a aT extended-env))))
                                         (error 'type-check "JYSS error: body return type not correct ~e" e)]
                            [else (type-check u extended-env)])]
    [(ifC test then else)
     (cond
       [(boolT? (type-check test tenv))
        (cond
          [(equal? (type-check then tenv)(type-check else tenv)) (type-check then tenv)]
          [else (error 'type-check "JYSS error: then and else type mismatch for if statement ~e ~e" then else)])]
       [else (error 'type-check "JYSS error: not a boolean test for if statement ~e" test)])]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; INTERP FUNCTIONS


; Interprets/evaluates the given expression
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(numC n) n]
    [(StringC str) str]
    [(IdC name) (env-lookup env name)]
    [(lamC arg argType funbody) (closV arg funbody env)]
    [(ifC test then else)
     (define eval-test (interp test env))
     (match eval-test
         [#t (interp then env)]
         [other (interp else env)])]
    [(recC fname args argsT retT body func-use)
     (define closEnv (extend-env (list fname) (list 0) env))
     (define func-useEnv (extend-env (list fname) (list (closV args body closEnv)) env))
     (Env-set-syb closEnv fname (closV args body closEnv))
     (interp func-use func-useEnv)]
    [(AppC func args) (define eval-args (interpManyArgs args func env))
                      (define interpFunc (interp func env))
                       (match interpFunc
                         [(closV params body clo-env)
                              (define new-env (extend-env params eval-args clo-env))
                              (interp body new-env)]
                         [(primV op) (interpprimV interpFunc eval-args)])]))


; Interprets/evaluates when given a primV
(define (interpprimV [op : primV] [args : (Listof Value)]) : Value
  (match (primV-op op)
    ['/ (match args
             [(list (? real? val1) (? real? val2))
              (if (equal? val2 0)
                  (error 'interpprimV "JYSS error: can't divide by 0 ~e" args)
                  ((primV-look-up (primV-op op)) val1 val2))])]
    ['substring (match args
                  [(list str begin end) (substring (cast str String) (cast begin Integer)
                                                   (cast end Integer))])]
    ['str-eq? (match args
                  [(list val1 val2) (equal? (cast val1 String) (cast val2 String))])]
    [other (match args
             [(list (? real? val1) (? real? val2)) ((primV-look-up (primV-op op)) val1 val2)])]))


; Function to interpret multiple args
(define (interpManyArgs [args : (Listof ExprC)] [func : ExprC] [env : Env]) : (Listof Value)
  (match args
    ['() '()]
    [(cons f r) (cons (interp f env) (interpManyArgs r func env))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Environment functions


; extends the environmnet to include new symbol
(define (extend-env [sybs : (Listof Symbol)] [values : (Listof Value)] [env : Env]) : Env
  (match sybs
    ['() env]
    [(cons f r) (Env (cons (Binding f (boxV (first values))) (Env-bindings (extend-env r (rest values) env))))]))


; looks up symbol in the environment and returns its value
(define (env-lookup [env : Env] [syb : Symbol]) : Value
  (match (Env-bindings env)
    ['() (error 'env-lookup "JYSS error: could not find symbol in environment ~e" syb)]
    [(cons f r) (cond
                  [(equal? (Binding-name f) syb) (unbox (Binding-val f))]
                  [else (env-lookup (Env r) syb)])]))

; looks up symbol in the environment and change its value
(define (Env-set-syb [env : Env] [syb : Symbol] [val : Value]) : Void
  (match (Env-bindings env)
    ['() (error 'TEnv-lookup "JYSS error: could not find symbol in environment ~e" syb)]
    [(cons f r) (cond
                  [(equal? (Binding-name f) syb) (set-box! (Binding-val f) val)]
                  [else (Env-set-syb (Env r) syb val)])]))

; extends the type environment to include new symbol and type
(define (extend-TEnv [sybs : (Listof Symbol)] [values : (Listof Ty)] [env : TEnv]) : TEnv
  (match sybs
    ['() env]
    [(cons f r) (TEnv (cons (TBinding f (first values)) (TEnv-TBindings (extend-TEnv r (rest values) env))))]))


; looks up symbol in the environment and returns its type
(define (TEnv-lookup [env : TEnv] [syb : Symbol]) : Ty
  (match (TEnv-TBindings env)
    ['() (error 'TEnv-lookup "JYSS error: could not find symbol in environment ~e" syb)]
    [(cons f r) (cond
                  [(equal? (TBinding-name f) syb) (TBinding-type f)]
                  [else (TEnv-lookup (TEnv r) syb)])]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; HELPER FUNCTIONS


; Maps primV names to their meanings
(define (primV-look-up [syb : Symbol]) :
  (U (-> Real * Real) (-> Real Real * Real) (Any Any -> Boolean) (Real Real -> Boolean))
  (match syb
    ['+  +]
    ['-  -]
    ['*  *]
    ['/  /]
    ['<= <=]
    ['num-eq? equal?]
    [other (error 'look-up "JYSS error: unimplemented operator ~e" syb)]))


; Accepts any JYSS5 value and returns a string
(define (serialize [val : Value]) : String
  (match val
    [(? real? num) (~v num)]
    [#t "true"]
    [#f "false"]
    [(primV op) "#<primV>"]
    [(closV arg body env) "#<procedure>"]
    [(? string? str) (~v str)]))


; Return true if a reserved keyword
(define (is-reserved [syb : Symbol]) : Boolean
  (match syb
    ['vars: #t]
    ['body: #t]
    ['if #t]
    ['proc #t]
    ['go #t]
    [': #t]
    ['= #t]
    ['in #t]
    ['rec #t]
    ['-> #t]
    ['=> #t]
    [other #f]))


; Return true if anything in list is a reserved keyword
(define (is-reserved-inList [arg : (Listof Symbol)]) : Boolean
  (match arg
    ['() #f]
    [(cons f r) (cond
                  [(is-reserved f) #t]
                  [else (is-reserved-inList r)])]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; TEST CASES

; Test cases for recursion
(check-exn (regexp (regexp-quote "JYSS error: body return type not correct"))
           (lambda () (type-check (parse '{rec: [f = {proc {[n : num]} : num go {if {<= n 0} true false}}]
                                           in {f 5}}) base-tenv)))
(check-equal? (top-interp '{rec: [f = {proc {[n : num]} : num go {if {<= n 0} 1 {* n {f {- n 1}}}}}]
                            in {f 5}}) "120")
(check-equal? (top-interp '{rec: [square-helper =
                                    {proc {[n : num]} : num go
                                          {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}]
                            in
                              {vars: [square : {num -> num}  =
                                       {proc {[n : num]} go {square-helper {- {* 2 n} 1}}}]
                               body: {square 13}}})
              "169")
(check-exn (regexp (regexp-quote "JYSS error: function name is reserved"))
          (lambda () (top-interp '{rec: [: = {proc {[n : num]} : num go {if {<= n 0} 1 {* n {f {- n 1}}}}}]
                                   in {f 5}})))
(check-exn (regexp (regexp-quote "JYSS error: could not find symbol in environment"))
          (lambda ()  (Env-set-syb top-env 'a 10)))

; Setting up testing environments for types
(define empty-TEnv (TEnv '()))
(define ex-Tenv (TEnv (list (TBinding 's+ (funT (list (strT) (strT)) (numT)))
                            (TBinding 'x (numT))
                            (TBinding 'z (strT))
                            (TBinding '< (funT (list (numT) (numT)) (boolT)))
                            (TBinding '+ (funT (list (numT) (numT)) (numT))))))
(define test-TEnv (TEnv (list (TBinding 'a (numT)) (TBinding 'e (boolT)) (TBinding 'q (strT)))))

; Test cases for parse-arg
(check-equal? (parse-arg '[x : num]) (numT))
(check-equal? (parse-arg '[x : bool]) (boolT))
(check-equal? (parse-arg '[x : str]) (strT))
(check-equal? (parse-arg '[x : num = 5]) (numT))
(check-equal? (parse-arg '[x : bool = true]) (boolT))
(check-equal? (parse-arg '[x : str = hello]) (strT))
(check-equal? (parse-type '(num num -> str)) (funT (list (numT) (numT)) (strT)))

; Test cases for some helper functions when parsing
(check-equal? (getArgNames '{[z : num = {+ 9 14}] [y : num = 98]}) '(z y))
(check-equal? (getArgValues '{[z : num = {+ 9 14}] [y : num = 98]}) '({+ 9 14} 98))

; Test cases for desugar
(check-equal? (desugar '{vars: [x : num = 7] [z : str = "hey"] body: {+ x 2}})
              '((proc ((x : num) (z : str)) go (+ x 2)) 7 "hey"))

; Test cases for TEnv-lookup & extend-TEnv
(check-equal? (TEnv-lookup test-TEnv 'a) (numT))
(check-equal? (TEnv-lookup test-TEnv 'q) (strT))
(check-equal? (TEnv-lookup test-TEnv 'e) (boolT))
(check-equal? (extend-TEnv '(b c) (list (numT) (strT)) test-TEnv)
              (TEnv (list (TBinding 'b (numT)) (TBinding 'c (strT))
                          (TBinding 'a (numT)) (TBinding 'e (boolT)) (TBinding 'q (strT)))))
(check-exn (regexp (regexp-quote  "JYSS error: could not find symbol in environment"))
           (lambda () (TEnv-lookup test-TEnv 'hj)))

; Test cases for parse
(check-equal? (parse '{proc {[n : num] [z : str] [a : bool]} go {+ n 1}})
              (lamC '(n z a) (list (numT) (strT) (boolT)) (AppC (IdC '+) (list (IdC 'n) (numC 1)))))
(check-equal? (parse '{{proc {[x : num] [z : str]} go {+ x 2}} 7 "hey"})
       (AppC (lamC '(x z) (list (numT) (strT))
                   (AppC (IdC '+) (list (IdC 'x) (numC 2)))) (list (numC 7) (StringC "hey"))))
(check-equal? (parse '{vars: [x : num = 7] [z : str = "hey"] body: {+ x 2}})
       (AppC (lamC '(x z) (list (numT) (strT))
                   (AppC (IdC '+) (list (IdC 'x) (numC 2)))) (list (numC 7) (StringC "hey"))))

; Test cases for interp: primV +, /, *, -, <=
(check-equal? (interp (parse '{vars: [z : num = {+ 9 14}] [y : num = 98] body: {+ z y}}) top-env) 121)
(check-equal? (interp (parse '{vars: [z : num = {+ 20 10}] [y : num = 2] body: {- z y}}) top-env) 28)
(check-equal? (interp (parse '{vars: [z : num = {+ 20 10}] [y : num = 2] body: {/ z y}}) top-env) 15)
(check-equal? (interp (parse '{vars: [z : num = {* 20 10}] [y : num = 2] body: {* z y}}) top-env) 400)
(check-equal? (interp (parse '{vars: [z : num = {+ 20 10}] [y : num = 2] body: {<= z y}}) top-env) #f)
(check-equal? (interp (parse '{vars: [z : num = {+ 20 10}] [y : num = 30] body: {<= z y}}) top-env) #t)
(check-equal? (interp (parse '{{proc {[n : num] [z : str] [a : bool]} go {+ n 1}} 4 "hey" true}) top-env) 5)

; Test cases for interp: primV substring
(check-equal? (interp (parse '{vars: [x : str = "Apple"]
                                     [y : num = 1] [z : num = 3] body: {substring x y z}}) top-env) "pp")

; Test cases for interp:primV num-eq?, str-eq?
(check-equal? (interp (parse '{vars: [z : str = "Hello"] [y : str = "Hey"] body: {str-eq? z y}}) top-env) #f)
(check-equal? (interp (parse '{vars: [z : str = "Hello"] [y : str = "Hello"] body: {str-eq? z y}}) top-env) #t)
(check-equal? (interp (parse '{vars: [z : num = {+ 10 10}] [y : num = 98] body: {num-eq? z y}}) top-env) #f)
(check-equal? (interp (parse '{vars: [z : num = {+ 10 10}] [y : num = 20] body: {num-eq? z y}}) top-env) #t)
(check-equal? (interp (parse '{vars: [z : num = {+ 10 10}] [y : num = 30] body: {if true z y}}) top-env) 20)

; Type Checking base values
(check-equal? (type-check (numC 10) base-tenv) (numT))
(check-equal? (type-check (StringC "hey") base-tenv) (strT))
(check-equal? (type-check (numC 1) empty-TEnv) (numT))

; Type Checking AppC
(check-equal? (type-check (AppC (IdC '+) (list (numC 5) (numC 10))) base-tenv) (numT))
(check-equal? (type-check (AppC (IdC '+) (list (numC 1) (numC 2))) ex-Tenv) (numT))
(check-equal? (type-check (AppC (IdC 'str-eq?) (list (StringC "hello") (StringC "what"))) base-tenv) (boolT))
(check-exn (regexp (regexp-quote  "JYSS error: app arg mismatch"))
           (lambda () (type-check (AppC (IdC '+) (list (StringC "hello") (StringC "what"))) base-tenv)))
(check-exn (regexp (regexp-quote  "JYSS error: app arg mismatch"))
           (lambda () (top-interp '{vars: [z : {num num -> num} = +] [y : num = 98] body: {num-eq? z y}})))
(check-exn (regexp (regexp-quote  "JYSS error: not a function"))
           (lambda () (type-check (AppC (IdC 'true) (list (numC 10))) base-tenv)))

 ; Type Checking LamC
(check-equal? (type-check (lamC (list 'x 'y) (list (strT) (strT))
                                 (AppC (IdC 's+) (list (StringC "a") (StringC "b")))) ex-Tenv)
              (funT (list (strT) (strT)) (numT)))

; Type Checking if statements
(check-equal? (type-check (ifC (AppC (IdC '<) (list (numC 1) (numC 2)))
                                 (StringC "true") (StringC "false"))
                                  ex-Tenv) (strT))
(check-exn (regexp (regexp-quote  "JYSS error: not a boolean test for if statement"))
           (lambda () (type-check (ifC (AppC (IdC '+) (list (numC 1) (numC 2)))
                                         (numC 1) (numC 0)) ex-Tenv)))
(check-exn (regexp (regexp-quote  "JYSS error: then and else type mismatch for if statement"))
          (lambda () (type-check (ifC (AppC (IdC '<) (list (numC 1) (numC 2)))
                                         (numC 1) (StringC "hey")) ex-Tenv)))

; Serialize tests
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize 77) "77")
(check-equal? (serialize (primV'+)) "#<primV>")
(check-equal? (serialize "Hey!") "\"Hey!\"")
(check-equal? (serialize (closV (list 'a 'b) (numC 10) top-env)) "#<procedure>")


; Passing tests for interp
(check-equal? (top-interp '{vars: [z : num = {+ 9 14}] [y : num = 98] body: {+ z y}}) "121")
(check-exn (regexp (regexp-quote  "JYSS error: app arg mismatch"))
           (lambda ()  (top-interp '{vars: [z : {num num -> num} = +] [y : num = 98] body: {num-eq? z y}})))
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (IdC 'z))
                            (list (numC 9) (numC 10)))
                      top-env)
              9)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC '+)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 9) (numC 10)))
                      top-env)
              19)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC '-)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 10) (numC 9)))
                      top-env)
              1)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC '*)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 10) (numC 9)))
                      top-env)
              90)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC '<=)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 10) (numC 9)))
                      top-env)
              #f)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC 'num-eq?)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 10) (numC 9)))
                      top-env)
              #f)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC '<=)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 9) (numC 10)))
                      top-env)
              #t)
(check-equal? (interp (AppC (lamC (list 'z 'y)
                                  (list (numT) (numT))
                                  (AppC (IdC '/)
                                        (list (IdC 'z) (IdC 'y))))
                            (list (numC 10) (numC 2)))
                      top-env)
              5)
(check-equal? (interp (ifC (AppC (IdC 'num-eq?)
                                 (list (numC 5) (numC 10)))
                           (numC 1)
                           (numC 0))
                      top-env)
              0)
(check-equal? (interp (ifC (AppC (IdC '<=) (list (numC 5) (numC 10)))
                           (numC 1)
                           (numC 0))
                      top-env)
              1)

; Setting argument name to reserved keyword
(check-exn (regexp (regexp-quote  "JYSS error: arg names can't be reserved keywords"))
           (lambda () (parse '{vars: [if : num = {+ 9 14}] [y : num = 98] body: {+ if y}})))
(check-exn (regexp (regexp-quote  "JYSS error: arg names can't be reserved keywords"))
           (lambda () (parse '{vars: [proc : num = {+ 9 14}] [y : num = 98] body: {+ if y}})))

; Can't divide by 0
(check-exn (regexp (regexp-quote  "JYSS error: can't divide by 0"))
           (lambda ()  (interp (AppC (lamC (list 'z 'y)
                                           (list (numT) (numT))
                                           (AppC (IdC '/)
                                                 (list (IdC 'z) (IdC 'y))))
                                     (list (numC 10) (numC 0))) top-env)))

; Wrong number of arguments given to primV functions
(check-exn (regexp (regexp-quote  "JYSS error: wrong number of arguments provided"))
           (lambda ()  (top-interp '{vars: [z : num = {+ 9 14 4}] [y : num = 98] body: {+ z y}}) ))
(check-exn (regexp (regexp-quote  "JYSS error: wrong number of arguments provided"))
           (lambda ()  (top-interp'{vars: [z : num = {/ 9 14 4}] [y : num = 98] body: {+ z y}})))
(check-exn (regexp (regexp-quote  "JYSS error: wrong number of arguments provided"))
           (lambda ()  (top-interp '{vars: [z : num = {num-eq? 9 14 4}] [y : num = 98] body: {+ z y}})))

; Wrong type of arguments given to primV functions
(check-exn (regexp (regexp-quote  "JYSS error: app arg mismatch"))
           (lambda ()  (top-interp '{vars: [z : num = {+ 9 "Hello"}] [y : num = 98] body: {+ z y}})))
(check-exn (regexp (regexp-quote  "JYSS error: app arg mismatch"))
           (lambda ()  (top-interp '{vars: [z : num = {/ 9 "Hello"}] [y : num = 98] body: {+ z y}})))
(check-exn (regexp (regexp-quote "JYSS error: mulitple args with same name"))
           (lambda () (parse '{vars: [z : num = {+ 9 14}] [z : num = 98] body: {+ z z}})))

; Wrong format for vars format
(check-exn (regexp (regexp-quote "JYSS error: arg names can't be reserved keywords '(go)"))
           (lambda () (parse '(vars: (go : str = "") body: "World"))))
(check-exn (regexp (regexp-quote "JYSS error: wrong format given"))
           (lambda () (parse '{vars: [z : num = ] [z : num = 98] body: {+ z z}})))
(check-exn (regexp (regexp-quote "JYSS error: wrong format given"))
           (lambda () (parse '{vars: [z ? {+ 1 3}] [z : num = 98] body: {+ z z}})))

; No matching pattern for expression in parse
(check-exn (regexp (regexp-quote  "JYSS error: invalid expression given #t"))
           (lambda () (parse #t)))

; Wrong format for if statement
(check-exn (regexp (regexp-quote "JYSS error: Incorrect format for if statement"))
           (lambda () (parse '(if (num-eq? 5 10) 1 0 3))))

; Tests for environment functions
(check-equal? (env-lookup (Env (list (Binding 'a (boxV 1))
                                     (Binding 'b (boxV 2)) (Binding 'c (boxV 3)))) 'a) 1)
(check-equal? (env-lookup (Env (list (Binding 'a (boxV 1))
                                     (Binding 'b (boxV 2)) (Binding 'c (boxV 3)))) 'c) 3)
(check-equal? (extend-env (list 'a 'b 'c) (list 1 2 3) empty-Env)
              (Env (list (Binding 'a (boxV 1)) (Binding 'b (boxV 2)) (Binding 'c (boxV 3)))))
(check-exn (regexp (regexp-quote  "JYSS error: could not find symbol"))
           (lambda () (interp (IdC 'y) empty-Env)))

; Tests for is-reserved
(check-equal? (is-reserved 'body:) #t)
(check-equal? (is-reserved 'go) #t)
(check-equal? (is-reserved 'proc) #t)
(check-equal? (is-reserved 'vars:) #t)
(check-equal? (is-reserved ':) #t)
(check-equal? (is-reserved '=) #t)
(check-equal? (is-reserved 'in) #t)
(check-equal? (is-reserved 'rec) #t)
(check-equal? (is-reserved '->) #t)
(check-equal? (is-reserved '=>) #t)

; For primV-look-up
(check-exn (regexp (regexp-quote  "JYSS error: unimplemented operator"))
           (lambda () (primV-look-up '&)))

; For top-interp
(check-equal? (top-interp '{vars: [z : num = {+ 9 14}] [y : num = 98] body: {+ z y}}) "121")
(check-equal? (top-interp '{+ 1 14}) "15")
(check-equal? (top-interp '{{proc {[x : num]} go {+ {{proc {[y : num]} go {+ y 14}} 1}
                                     1}} 1} )"16")
(check-exn (regexp (regexp-quote  "JYSS error: can't divide by 0"))
           (lambda ()  (top-interp '{{proc {[x : num]} go {+ 3 4}} {/ 1 {+ 0 0}}})))

; Test if statement
(check-equal? (top-interp '{{proc {[x : bool] [y : num]} go {if x {- y 1} {+ y 1}}} {<= 1 2} 2} ) "1")
(check-equal? (top-interp '{{proc {[y : num]} go
                                  {if {{proc {[x : num]} go {<= x 0}} 1} {- y 1}
                                      {+ y 1}}} 2}) "3")

; Extra paranthesis in argument name
(check-exn (regexp (regexp-quote  "JYSS error: Wrong format given"))
           (lambda () (top-interp '{{proc {{[x : num]}} go {+ {* x 2} 14}} 1})))

; For parse
(check-equal? (parse '{area 3 4}) (AppC (IdC 'area) (list (numC 3) (numC 4))))
(check-equal? (parse '{five}) (AppC (IdC 'five) '()))
(check-equal? (parse '{area "hello" 4}) (AppC (IdC 'area) (list (StringC "hello") (numC 4))))
(check-equal? (parse '{{{g {z}} 9}})
              (AppC (AppC (AppC (IdC 'g) (list (AppC (IdC 'z) (list)))) (list (numC 9))) (list)))

; Passing in wrong pattern to desugar
(check-exn (regexp (regexp-quote  "JYSS error: should never reach here"))
           (lambda () (desugar '{vars: [z = {+ 9 14}] [y = 98] {+ z y}})))


; Variable name as reserved keyword
(check-exn (regexp (regexp-quote  "JYSS error: variable name can't be reserved keyword"))
           (lambda ()  (top-interp '{if {< go 0} 3 4})))

; Wrong format given when parsing arguments for vars and proc
(check-exn (regexp (regexp-quote "JYSS error: wrong format given"))
           (lambda () (getArgValues '{[z {+ 1 3}]})))
(check-exn (regexp (regexp-quote "JYSS error: Wrong format given"))
           (lambda () (parse-type-sexp '{[z {+ 1 3}]})))

; test cases for parse
(check-equal? (parse '{proc {[x : num]} go {+ x 1}})
              (lamC '(x) (list (numT)) (AppC (IdC '+) (list (IdC 'x) (numC 1)))))
(check-equal? (parse '{proc {[x : num] [y : str]} go {+ x y}})
              (lamC '(x y) (list (numT) (strT)) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))))
(check-equal? (parse '{vars: [x : num = 3] body: {+ x 1}})
              (AppC (lamC '(x) (list (numT)) (AppC (IdC '+) (list (IdC 'x) (numC 1))))
                    (list (numC 3))))
(check-equal? (parse '{vars: [x : {bool num -> num} =
                                {proc {[a : bool] [b : num]} go {if {equal? a true}
                                                                  {* b 100}
                                                                   {+ b 1}}}]
                             [y : bool = true]
                             [z : num = 10]
                       body: {x y z}})
              (AppC (lamC '(x y z)
                          (list (funT (list (boolT) (numT)) (numT)) (boolT) (numT))
                          (AppC (IdC 'x) (list (IdC 'y) (IdC 'z))))
                    (list (lamC '(a b)
                                (list (boolT) (numT))
                                (ifC (AppC (IdC 'equal?) (list (IdC 'a) (IdC 'true)))
                                     (AppC (IdC '*) (list (IdC 'b) (numC 100)))
                                     (AppC (IdC '+) (list (IdC 'b) (numC 1)))))
                          (IdC 'true)
                          (numC 10))))

; Code-Coverage
(check-exn (regexp (regexp-quote  "JYSS error: wrong format given"))
           (lambda () (getArgValues '[x := 3])))
(check-exn (regexp (regexp-quote  "JYSS error: Wrong format given"))
           (lambda () (parse-type-sexp '[x = 3])))
(check-equal? (parse-type-sexp '[x : num = 4]) 'num)
(check-equal? (parse-type-sexp '[x : num]) 'num)
(check-exn (regexp (regexp-quote  "JYSS error: Wrong format given"))
           (lambda () (parse-arg-name '[x = 3])))
(check-equal? (parse-arg-name '[x : num = 3]) 'x)
(check-exn (regexp (regexp-quote  "JYSS error: Type not supported"))
           (lambda () (parse-type 'Real)))

