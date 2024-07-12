#lang typed/racket
(require typed/rackunit)

; Implemented full project

; Defines a new language ZODE with as per the spec
(define-type ExprC (U numC ifC idC appC lambC strC boolC recC))
(struct numC ([n : Real]) #:transparent)
(struct strC ([s : String]) #:transparent)
(struct boolC ([b : Boolean]))
(struct ifC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct idC ([name : Symbol]) #:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lambC ([arglst : (Listof (Pair Ty Symbol))] [return-type : (Option Ty)] [body : ExprC]) #:transparent)
(struct recC ([name : Symbol]
              [arglst : (Listof (Pair Ty Symbol))]
              [return-type : Ty]
              [body : ExprC]
              [usage : ExprC]) #:transparent)

; Defines the types that ZODE supports
; I don't know how to make it so they dont take a value
; The Value of the types are fully pointless
; I created a helper function to test for equality
; Which ignores the values. This leads to some pretty
; Ugly code, but I can't figure out how to create a struct
; without any fields.
(define-type Ty (U numT boolT strT arrowT (Listof Ty)))
(struct numT ([val : Real]) #:transparent)
(struct boolT ([val : Boolean]) #:transparent)
(struct strT ([val : String]) #:transparent)
(struct arrowT ([left : Ty] [right : Ty]) #:transparent)

; Defines the types of values that ZODE expects
(define-type Value (U Real Boolean String closV primop-numeric primop-num-eq primop-str-eq primop-substring))
(struct closV ([arglst : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primop-numeric ([name : Symbol]) #:transparent)
(struct primop-num-eq ([name : Symbol]) #:transparent)
(struct primop-str-eq ([name : Symbol]) #:transparent)
(struct primop-substring ([name : Symbol]) #:transparent)
;(struct primop-error ([name : Symbol]) #:transparent)


; Defines the environment datastructure
(define-type Env (Listof Binding))
(struct Binding ([name : Symbol] [val : (Boxof Value)]))

; binds top level definitions
(define-type TEnv (Listof TBinding))
(struct TBinding ([name : Symbol] [val : Ty]))

(define base-tenv (list
                  (TBinding 'true (boolT #t))
                  (TBinding 'false (boolT #f))
                  (TBinding '+ (arrowT (list (numT 0) (numT 0)) (numT 0)))
                  (TBinding '- (arrowT (list (numT 0) (numT 0)) (numT 0)))
                  (TBinding '* (arrowT (list (numT 0) (numT 0)) (numT 0)))
                  (TBinding '/ (arrowT (list (numT 0) (numT 0)) (numT 0)))
                  (TBinding '<= (arrowT (list (numT 0) (numT 0)) (boolT #t)))
                  (TBinding 'num-eq? (arrowT (list (numT 0) (numT 0)) (boolT #t)))
                  (TBinding 'str-eq? (arrowT (list (strT "S") (strT "S")) (boolT #t)))
                  (TBinding 'substring (arrowT (list (strT "s") (numT 0) (numT 0)) (boolT #t)))))


(define mt-env (list
                (Binding 'true (box #t))
                (Binding 'false (box #f))
                (Binding '+ (box (primop-numeric '+)))
                (Binding '- (box (primop-numeric '-)))
                (Binding '* (box (primop-numeric '*)))
                (Binding '/ (box (primop-numeric '/)))
                (Binding '<= (box (primop-numeric '<=)))
                ;(Binding 'equal? (box (primop-bool 'equal?)))
                (Binding 'num-eq? (box (primop-num-eq 'num-eq?)))
                (Binding 'str-eq? (box (primop-str-eq 'str-eq?)))
                (Binding 'substring (box (primop-substring 'substring)))))
                ;(Binding 'error (primop-error 'error))))

; Serializes a ZODE 4 expression
(define (serialize [val : Value]) : String
  (match val
    [(? real? n) (format "~v" n)]
    [(? boolean? b) (if b "true" "false")]
    [(? closV? closure) "#<procedure>"]
    [(? primop-numeric? prim) "#<primop>"]
    [(? string? s) (format "~v" s)]))

; Creates the top level type environment
(define (create-top-tenv) : TEnv
  (define base-tenv (list
                     (TBinding 'true (boolT #t))
                     (TBinding 'false (boolT #f))
                     (TBinding '+ (arrowT (list (numT 0) (numT 0)) (numT 0)))
                     (TBinding '- (arrowT (list (numT 0) (numT 0)) (numT 0)))
                     (TBinding '* (arrowT (list (numT 0) (numT 0)) (numT 0)))
                     (TBinding '/ (arrowT (list (numT 0) (numT 0)) (numT 0)))
                     (TBinding '<= (arrowT (list (numT 0) (numT 0)) (boolT #t)))
                     (TBinding 'num-eq? (arrowT (list (numT 0) (numT 0)) (boolT #t)))
                     (TBinding 'str-eq? (arrowT (list (strT "S") (strT "S")) (boolT #t)))
                     (TBinding 'substring (arrowT (list (strT "s") (numT 0) (numT 0)) (boolT #t)))))
  base-tenv)

; Creates the top level environment
(define (create-top-env) : Env
  (define mt-env (list
                  (Binding 'true (box #t))
                  (Binding 'false (box #f))
                  (Binding '+ (box (primop-numeric '+)))
                  (Binding '- (box (primop-numeric '-)))
                  (Binding '* (box (primop-numeric '*)))
                  (Binding '/ (box (primop-numeric '/)))
                  (Binding '<= (box (primop-numeric '<=)))
                  (Binding 'num-eq? (box (primop-num-eq 'num-eq?)))
                  (Binding 'str-eq? (box (primop-str-eq 'str-eq?)))
                  (Binding 'substring (box (primop-substring 'substring)))))
  mt-env)

; Accepts an s-expression in the ZODE language and evaluates it, serializing the result
(define (top-interp [s : Sexp]) : String
  (define parsed-code (parse s))
  (type-check parsed-code (create-top-tenv))
  (serialize (interp parsed-code (create-top-env))))

; Accepts an s-expression and parses it into an ZODE expression
(define (parse [s : Sexp]) : ExprC
  (match s
    [(list 'local-rec ': (? symbol? id) '= lamb-def ': usage)
     (define parsed-lamb (parse lamb-def))
     ;(printf "parsed-lamb ~s\n" parsed-lamb)
     (cond
       [(lambC? parsed-lamb)
        (define ret-type (lambC-return-type parsed-lamb))
        (recC id (lambC-arglst parsed-lamb) (cast ret-type Ty) (lambC-body parsed-lamb) (parse usage))]
        ; This code checks that the lambda actually has a return type,
        ; but the only way it wont, is if it was some sort of local definition
        ; in which case it would be parsed as an appC, and could never get here.
        ; I dont think its useful, but leaving as vestigial code. 
        ;(cond
        ;  [(equal? ret-type #f) (error 'parse "ZODE Invalid local-rec definition lamb with no return type...")]
        ;  [else 
        ;   (recC id (lambC-arglst parsed-lamb) ret-type (lambC-body parsed-lamb) (parse usage))])]
       [else (error 'parse "ZODE Invalid local-rec definition")])]
    [(list 'locals ': args ...) (parse (desugar args))]
    [(list 'lamb ': vars ... '-> return-type ': body)
     (define varlist (get-symbols (cast vars (Listof Sexp))))
     (define identifiers (strip-identifiers varlist))
     (cond
       [(duplicate-args? identifiers) (error 'parse "ZODE Duplicate variable names")]
       [(invalid-params? identifiers) (error 'parse "ZODE Can't use keywords as variable names")]
       [(equal? 'false return-type)
        (lambC varlist #f (parse body))]
       [else (lambC varlist (parse-type return-type) (parse body))])]
    [(list (? list? body) args ...)
     (appC (parse body) (map parse args))]
    [(list 'if ': test ': then ': else) (ifC (parse test) (parse then) (parse else))]
    [(list firstval args ...) (appC (parse firstval) (map parse args))]
    [(? symbol? arg)
     (cond
       [(invalid-params? (list arg)) (error 'parse "ZODE Can't use keywords as variable names: Invalid args ~s" arg)]
       [else (idC arg)])]
    [(? real? n) (numC n)]
    [(? string? s) (strC s)]))

; Accepts a ZODE4 expression and interprets it
(define (interp [a : ExprC] [env : Env]) : Value
  (match a
    [(numC n) n]
    [(strC s) s]
    [(recC name args ret-type body usage)
     (define extended-env (extend-env (list (Binding name (box #f))) env))
     (define closure (closV (strip-identifiers args) body extended-env))
     (extend-env (list (Binding name (box closure))) extended-env)
     (interp usage extended-env)]
    [(appC fun args)
     (define fun-val (interp fun env))
     (cond
       [(primop-numeric? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (define cleaned-args (clean-primparams processed-args))
        (cond
          [else (define left (first cleaned-args))
                (define right (first (rest cleaned-args)))
                (match (primop-numeric-name fun-val)
                  ['+ (+ left right)]
                  ['- (- left right)]
                  ['* (* left right)]
                  ['/
                   (if (equal? right 0)
                       (error 'interp "ZODE Divide by 0 error")
                       (/ left right))]
                  ['<= (<= left right)]
                  )])]
       [(primop-num-eq? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (equal? (first processed-args) (first (rest processed-args)))]
       [(primop-str-eq? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (equal? (first processed-args) (first (rest processed-args)))]
       [(primop-substring? fun-val)
        (define str (interp (first args) env))
        (define from (interp (first (rest args)) env))
        (define to (interp (first (rest (rest args))) env))
        (cond
          [(and (string? str) (integer? from) (integer? to))
           (substring str (cast from Integer) (cast to Integer))]
          [else
           (error 'interp "ZODE substring, Expected string integer integer, but got: ~a, ~a, ~a" str from to)])]
       [(closV? fun-val)
        (define bindings
          (zip (closV-arglst (cast fun-val closV))
               (map
                (lambda ([arg : ExprC]) : Value (interp arg env))
                args)))
        (define extended-env (extend-env bindings (closV-env fun-val)))
        (interp (closV-body fun-val) extended-env)]
       [else
        (error 'interp "ZODE function did not eval to closure, bad-function: ~s" fun-val)])]
    [(lambC args ret-type body)
     (closV (strip-identifiers args) body env)]
    [(ifC test then else)
     (define result (interp test env))
     (if result (interp then env) (interp else env))]
    [(idC val) (lookup val env)]))

; Parses the types
(define (parse-type [s : Sexp]) : Ty
  (match s
    [(list args ... '-> return-type)
     (arrowT (parse-type (cast args Sexp)) (parse-type return-type))]
    [(list args ...) (map parse-type args)]
    [(? symbol? sym)
     (match sym
       ['num (numT 0)]
       ['str (strT "s")]
       ['bool (boolT #t)])]
    [else (error 'parse-type "ZODE Invalid type ~s" s)]))

; Checks a parsed ExprC for correct types.
(define (type-check [e : ExprC] [env : TEnv]) : Ty
  (match e
    [(numC n) (numT n)]
    [(strC s) (strT s)]
    [(idC id) (type-lookup id env)]
    [(boolC b) (boolT b)]
    [(ifC test then else)
     (if
       (not (check-same-type (boolT #t) (type-check test env)))
       (error 'type-check "ZODE type if test non-boolean")
       (if (not (check-same-type (type-check then env) (type-check else env)))
           (error 'type-check "ZODE if then else have different types")
           (type-check then env)))]
    [(lambC args ret-type body)
     (cond
       [(equal? ret-type #f)
        (arrowT (strip-types args) (boolT #f))]
       [else
        (define parsed-ret-type (cast ret-type Ty))
        ; I know cast is bad, but the above check forces it to be a type
        (define bindings
          (zip-types (strip-identifiers args) (strip-types args)))
        (define extended-env (extend-tenv bindings env))
        (define body-return (type-check body extended-env))
        (if (check-same-type body-return parsed-ret-type)
            (arrowT (strip-types args) parsed-ret-type)
            (error 'type-check "ZODE Lamb return type does not match body"))])]
    [(recC name arglst ret-type body usage)
     (define arg-types (strip-types arglst))
     (define extended-env (extend-tenv (list (TBinding name (arrowT arg-types ret-type))) env))
     (cond
       [(not
         (equal? ret-type
                 (type-check body (extend-tenv (zip-types (strip-identifiers arglst) (strip-types arglst))
                                               extended-env))))
        (error 'type-check "ZODE recC body reutrn type invalid")]
       [else
        (type-check usage extended-env)])]
    [(appC fun args)
     (define fun-type (type-check fun env))
     (cond
       [(arrowT? fun-type)
        (define arg-types (map (lambda ([arg : ExprC]) : Ty (type-check arg env)) args))
        (define expected-types (arrowT-left fun-type))
        (if (check-multi-types (cast expected-types (Listof Ty)) arg-types)
            (arrowT-right fun-type)
            (error 'type-check "ZODE invalid arguments passed while type-checking \nProvided: ~s\n Expected: ~s\n"
                   arg-types expected-types))]
       [else (error 'type-check "ZODE type-checking, trying to call non-function")])]))

; Checks a list of types against a list of expected types
(define (check-multi-types [expected : (Listof Ty)] [provided : (Listof Ty)]) : Boolean
    (match (list expected provided)
    [(list '() '()) #t]
    [(list (cons f-expected r-expected) '()) (error 'check-multi-types "ZODE TYPE Invalid number of params")]
    [(list '() (cons f-provided r-provided)) (error 'check-multi-types "ZODE TYPE Invalid number of params")]
    [(list (cons f-expected r-expected) (cons f-provided r-provided))
     (if (check-same-type f-expected f-provided)
         (check-multi-types r-expected r-provided)
         #f)]))

; Lookups a identifier in the type environment
(define (type-lookup [for : Symbol] [env : TEnv]): Ty
  (cond
    [(empty? env) (error 'lookup "ZODE Type Unbound identifier ~s" for)]
    [else (cond
            [(symbol=? for (TBinding-name (first env)))
             (TBinding-val (first env))]
            [else (type-lookup for (rest env))])]))

; Checks that two types are actually the same type
(define (check-same-type [one : Ty] [two : Ty]) : Boolean
  (cond
    [(and (numT? one) (numT? two)) #t]
    [(and (strT? one) (strT? two)) #t]
    [(and (boolT? one) (boolT? two)) #t]
    [(and (arrowT? one) (arrowT? two))
     (define one-left (arrowT-left one))
     (define two-left (arrowT-left two))
     (cond
       [(and (list? one-left) (list? two-left))
        (cond
          [(and (check-same-type (arrowT-right one) (arrowT-right two))
                (check-same-type-list (arrowT-left one) (arrowT-left two))) #t]
          [else #f])]
       [else
        (cond
          [(and (check-same-type (arrowT-right one) (arrowT-right two)) (check-same-type one-left two-left)) #t]
          [else
           #f])])]
    [else #f]))

; Checks if two list of types contain the same elements
(define (check-same-type-list [list1 : (Listof Ty)] [list2 : (Listof Ty)]) : Boolean
  (and (= (length list1) (length list2))
       (for/and: ([ty1 list1] [ty2 list2])
         (check-same-type ty1 ty2))))

; looks up an identifier in the environment and returns the value
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "ZODE Unbound identifier ~s" for)]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (unbox (Binding-val (first env)))]
            [else (lookup for (rest env))])]))

; Zips two lists together
(define (zip [what : (Listof Symbol)] [to : (Listof Value)]) : (Listof Binding)
  (match (list what to)
    [(list '() '()) '()]
    [(list (cons f-what r-what) '()) (error 'zip "ZODE Invalid number of params")]
    [(list '() (cons f-to r-to)) (error 'zip "ZODE Invalid number of params")]
    [(list (cons f-what r-what) (cons f-to r-to)) (cons (Binding f-what (box f-to)) (zip r-what r-to))]))

; Zips a list of symbols and types together
(define (zip-types [what : (Listof Symbol)] [to : (Listof Ty)]) : (Listof TBinding)
  (match (list what to)
    [(list '() '()) '()]
    [(list (cons f-what r-what) (cons f-to r-to)) (cons (TBinding f-what f-to) (zip-types r-what r-to))]))

; Binds multiple params to their values, replacing old bindings if they have the same name
(define (extend-env [bindings : (Listof Binding)] [env : Env]) : Env
  (cond
    [(empty? bindings)
     env]
    [(empty? env)
     (cons (first bindings) (extend-env (rest bindings) env))]
    [else
     (define first-env (first env))
     (define first-bind (first bindings))
     (cond
       [(symbol=? (Binding-name first-env) (Binding-name first-bind))
        (set-box! (Binding-val first-env) (unbox (Binding-val first-bind)))
        (cons first-env (extend-env (rest bindings) env))]
       [else
        (cons first-env (extend-env bindings (rest env)))])]))


; Binds multiple params to their values, replacing old bindings if they have the same name
(define (extend-tenv [bindings : (Listof TBinding)] [env : TEnv]) : TEnv
  (cond
    [(empty? bindings)
     env]
    [(empty? env)
     (cons (first bindings) (extend-tenv (rest bindings) env))]
    [else
     (define first-env (first env))
     (define first-bind (first bindings))
     (cond
       [(symbol=? (TBinding-name first-env) (TBinding-name first-bind))
        (cons first-bind (extend-tenv (rest bindings) env))]
       [else
        (cons first-env (extend-tenv bindings (rest env)))])]))


; Cleans primitive params, looks for only numeric
(define (clean-primparams [params : (Listof Value)]) : (Listof Real)
  (cond
    [(empty? params) '()]
    [else
     (cons (cast (first params) Real) (clean-primparams (rest params)))]))

; Strips just the symbols for a list of Typed Symbols
(define (strip-identifiers [args : (Listof (Pair Ty Symbol))]) : (Listof Symbol)
  (cond
    [(empty? args) '()]
    [else
     (cons (cdr (first args)) (strip-identifiers (rest args)))]))

; Strips just the types for a list of typed symbols
(define (strip-types [args : (Listof (Pair Ty Symbol))]) : (Listof Ty)
  (cond
    [(empty? args) '()]
    [else
     (cons (car (first args)) (strip-types (rest args)))]))

; Determines if there are duplicate arguments
(define (duplicate-args? [args : (Listof Symbol)]) : Boolean
  (cond
     [(empty? args) #f] 
     [(not (not (member (first args) (rest args)))) #t]
     [else (duplicate-args? (rest args))]))

; Determines if keywors are being used as params
(define (invalid-params? [args : (Listof Symbol)]) : Boolean
  (cond
    [(empty? args) #f]
    [(or (symbol=? (first args) 'locals)
         (symbol=? (first args) 'if)
         (symbol=? (first args) 'lamb)
         (symbol=? (first args) ':)
         (symbol=? (first args) '=)) #t]
    [else (invalid-params? (rest args))]))

; Gets the symbols from a list of Sexp, returns the types and symbols
(define (get-symbols [args : (Listof Sexp)]) : (Listof (Pair Ty Symbol))
  (cond
    [(empty? args) '()]
    [(match (first args)
       [(list ty sym)
        (if (not (symbol? sym))
            (error 'get-symbols "ZODE Vars not entierly symbols")
            (cons (cons (parse-type ty) sym) (get-symbols (rest args))))])]))


; Desugars, splits the locals definitions into the variables, the body of the main lamb, and the bodies of the
(define (split-desugar [s : Sexp] [vars : (Listof Sexp)] [bodies : (Listof Sexp)]) : (Listof Sexp)
  (match s
    [(list type (? symbol? varname) '= args ': remaining ...)
     (split-desugar remaining
                    (append vars (list (list type varname)))
                    (append bodies (list args)))]
    [(list body) 
     (list vars bodies body)]
    [else 
     (error 'split-desugar "ZODE Invalid locals definition")]))

; Desugars, wraps the main lamb into external lambs
(define (desugar [args : Sexp]) : Sexp
  (define desugar-results (split-desugar args '() '()))
  (define vars (first desugar-results))
  (define bodies (first (rest desugar-results)))
  (define body (first (rest (rest desugar-results))))
  (define varslist (cast vars (Listof Any)))
  (define bodieslist (cast bodies (Listof Any)))
  (cast (append (list (append (list 'lamb ':) varslist (list '-> 'false ':) (list body))) bodieslist) Sexp))

; Interp Tests
(check-equal? (interp (appC (idC '+) (list (numC 3) (numC 5))) mt-env) 8)
(check-equal? (interp (appC (idC '*) (list (numC 3) (numC 5))) mt-env) 15)
(check-equal? (interp (appC (idC '<=) (list (numC 3) (numC 5))) mt-env) #t)
(check-equal? (interp (appC (idC '<=) (list (numC 8) (numC 5))) mt-env) #f)
(check-equal? (interp (appC (idC '+) (list (appC (idC '*) (list (numC 2) (numC 4))) (numC 5))) mt-env) 13)
(check-equal? (interp (ifC (appC (idC '<=) (list (numC 4) (numC 0))) (idC 'true) (idC 'false)) mt-env) #f)
(check-equal? (interp (ifC (appC (idC '<=) (list (numC 3) (numC 4))) (numC 3) (numC 4)) mt-env) 3)
(check-equal? (interp (appC (idC '+) (list
                                      (numC 3)
                                      (appC (lambC (list (cons (numT 0) 'x))
                                                   (numT 0)
                                                   (appC (idC '+) (list (idC 'x) (idC 'x))))
                                            (list (numC 3))))) mt-env) 9)
(check-exn (regexp (regexp-quote "ZODE Unbound identifier"))
           (lambda () (interp (appC (idC '+) (list (numC 4) (idC 'x))) mt-env)))

(check-exn (regexp (regexp-quote "ZODE Invalid number of params"))
           (lambda () (interp
                       (appC (lambC (list (cons (numT 0) 'x))
                                    (numT 0)
                                    (appC (idC '+) (list (numC 1) (idC 'x))))
                             (list (numC 1) (numC 2))) mt-env)))
(check-exn (regexp (regexp-quote "ZODE Invalid number of params"))
           (lambda () (interp
                       (appC (lambC (list (cons (numT 0) 'x) (cons (numT 0) 'y) (cons (numT 0) 'z))
                                    (numT 0)
                                    (appC (idC '+) (list (numC 1) (idC 'x))))
                             (list (numC 1) (numC 2))) mt-env)))

; Type checks
(check-equal? (parse-type 'bool) (boolT #t))
(check-equal? (check-same-type (arrowT (numT 0) (numT 0)) (arrowT (numT 0) (numT 0))) #t)
(check-equal? (check-same-type (arrowT (numT 0) (numT 0)) (arrowT (boolT #t) (numT 0))) #f)
(check-equal? (check-same-type (arrowT (list (numT 0) (numT 0)) (numT 0))
                               (arrowT (list (numT 0) (boolT #t)) (numT 0))) #f)
(check-equal? (check-same-type (type-check (appC (idC '+) (list (numC 3) (numC 4))) base-tenv) (numT 0)) #t)
(check-equal?
 (check-same-type (type-check (appC (idC '+) (list (appC (idC '+) (list (numC 3) (numC 4))) (numC 5))) base-tenv)
                  (numT 0)) #t)
(check-equal? (check-same-type (type-check (ifC (boolC #t) (numC 3) (numC 4)) base-tenv) (numT 3)) #t)
(check-equal? (check-same-type (type-check (ifC (boolC #t) (strC "yuh") (strC "yeah!")) base-tenv) (strT "yeah")) #t)
(check-exn (regexp (regexp-quote "ZODE invalid arguments passed while type-checking"))
           (lambda () (type-check
                       (appC (idC '+) (list (strC "hey") (numC 4))) base-tenv)))
(check-exn (regexp (regexp-quote "ZODE TYPE Invalid number of params"))
           (lambda () (type-check
                       (appC (idC '+) (list (numC 3))) base-tenv)))
(check-exn (regexp (regexp-quote "ZODE TYPE Invalid number of params"))
           (lambda () (type-check
                       (appC (idC '+) (list (numC 3) (numC 3) (numC 3))) base-tenv)))
(check-exn (regexp (regexp-quote "ZODE Type Unbound identifier"))
           (lambda () (type-check
                       (appC (idC 'notplus) (list (numC 3) (numC 3) (numC 3))) base-tenv)))
(check-exn (regexp (regexp-quote "ZODE type if test non-boolean"))
           (lambda () (type-check
                       (ifC (numC 1) (numC 3) (numC 4)) base-tenv)))
(check-exn (regexp (regexp-quote "ZODE if then else have different types"))
           (lambda () (type-check
                       (ifC (boolC #t) (strC "yo") (numC 4)) base-tenv)))


; Parser Tests
(check-equal? (parse
               '{locals
                 : num z = {+ 9 14}
                 : num y = 98
                 : {+ z y}})
              (appC (lambC (list (cons (numT 0) 'z) (cons (numT 0) 'y))
                           #f
                           (appC (idC '+) (list (idC 'z) (idC 'y))))
                    (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
(check-equal? (parse
               '{if : 1 : 2 : 3})
               (ifC (numC 1) (numC 2) (numC 3)))
(check-equal? (parse '{+ 1 2})
              (appC (idC '+) (list (numC 1) (numC 2))))
(check-equal? (parse 1) (numC 1))
(check-equal? (parse '{* 1 2})
              (appC (idC '*) (list (numC 1) (numC 2))))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names")) (lambda () (parse '{+ if 4})))
(check-exn (regexp (regexp-quote "ZODE Duplicate variable names"))
           (lambda () (parse '{lamb : [num x] [num x] -> num : 1})))
(check-exn (regexp (regexp-quote "ZODE Vars not entierly symbols"))
           (lambda () (parse '{lamb :[num 1] [num 2] [num 3] -> num : 5})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{lamb : [num i] -> num : "Hello" 31/7 +})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{lamb : [num locals] -> num : 1})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{foo : i : "Hello" 31/7 +})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{= : i : "Hello" 31/7 +})))


; Top Interp Tests
(check-equal? (top-interp '{locals
              : num z = {+ 9 14}
              : num y = 98
              : {+ z y}}) "121")
(check-equal? (top-interp
               '{+ 1 2})
              "3")
(check-equal? (top-interp
               '{locals
                 : num x = 1
                 : num y = 2
                 : {- 1 {+ x y}}}) "-2")
(check-equal? (top-interp
               '{locals
                 : num x = 1
                 : num y = 2
                 : {/ 3 {+ x y}}}) "1")
(check-exn (regexp (regexp-quote "ZODE Divide by 0 error")) (lambda ()(top-interp
               '{locals
                 : num x = {+ 3 4}
                 : num y = {/ 1 {+ 0 0}}
                 : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE invalid arguments passed while type-checking"))
           (lambda () (top-interp
                       '{locals
                         : num x = {+ 1 true}
                         : num y = 4
                         : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         : num x
                         : num y = 4
                         : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         :
                         : num y = 4
                         : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         : num y = 4 num x = 3
                         : 1})))
(check-equal? (top-interp
               '{locals
                 : num x = 1
                 : num y = 1
                 : 1}) "1")
(check-exn (regexp (regexp-quote "ZODE type if test non-boolean"))
           (lambda () (top-interp
                      '{if : 1 : 2 : 3})))
(check-exn (regexp (regexp-quote "ZODE function did not eval to closure"))
           (lambda () (top-interp
                       '{locals
                         : num x = 1
                         : {x 1}})))
(check-equal? (top-interp
               '+) "#<primop>")
(check-equal? (top-interp
               '{lamb : [num x] -> num : {+ 1 x}}) "#<procedure>")
(check-equal? (top-interp
               '{if : true : true : false}) "true")
(check-equal? (top-interp
               '{if : true : false : true}) "false")
(check-exn (regexp (regexp-quote "ZODE TYPE Invalid number of params"))
           (lambda () (top-interp
                       '{+})))
(check-exn (regexp (regexp-quote "ZODE TYPE Invalid number of params"))
           (lambda () (top-interp
                       '{+ 2 3 4})))

(check-exn (regexp (regexp-quote "ZODE Invalid local-rec definition"))
           (lambda () (top-interp
                       '{local-rec : myfun = {locals : num x = 2 : x} : 3})))
;(check-equal? (top-interp
; '{{lamb : [{num -> num} seven] -> num : {seven}}
;   {{lamb : [{num num -> num} minus] -> num : {lamb : -> num : {minus {+ 3 10} {* 2 3}}}}
;    {lamb : [num x] [num y] -> num : {+ x {* -1 y}}}
;    }}) "7")
(check-equal? (top-interp
 '{{lamb : [num +] -> num : (* + +)} 14}) "196")
(check-exn (regexp (regexp-quote "ZODE type-checking, trying to call non-function"))
           (lambda () (top-interp '{3 4 5})))
;(check-exn (regexp (regexp-quote "user-error"))
;           (lambda () (top-interp
;                       '{+ 4 {error "1234"}})))
;(check-exn (regexp (regexp-quote "user-error"))
;           (lambda () (top-interp '{{lamb : e : {e e}} error})))
(check-equal? (top-interp '{locals
              : num x = 5
              : num y = 2
              : str successMSG = "Success!"
              : str failMSG = "Fail!"
              : {if : {<= {+ 5 2} {* 5 2}} : successMSG : failMSG}}) "\"Success!\"")

;(check-equal? (top-interp '{locals
;                            : []fact = {lamb : n self :
;                                           {if
;                                            : {equal? n 0}
;                                            : 1
;                                            : {* n {self {- n 1} self}}}}
;                           : {fact 5 fact}}) "120")
(check-equal? (parse '{local-rec : myfun = {lamb : [num x] [num y] -> num : {+ x y}} : {myfun 1 2}})
              (recC 'myfun (list (cons (numT 0) 'x) (cons (numT 0) 'y)) (numT 0)
                    (appC (idC '+) (list (idC 'x) (idC 'y))) (appC (idC 'myfun) (list (numC 1) (numC 2)))))
(check-equal? (type-check
               (parse '{local-rec : myfun = {lamb : [num x] [num y] -> num : {+ x y}} : {myfun 1 2}}) base-tenv)
              (numT 0))
(check-equal? (top-interp '{local-rec : myfun = {lamb : [num x] [num y] -> num : {+ x y}} : {myfun 1 2}}) "3")
;(parse '{local-rec : myfun = {lamb : [num x] [num y] -> num : {+ x y}} : {myfun 1 2}})

;(parse '{locals : {num num -> num} myfun = {lamb : [num x] [num y] -> num : {+ x y}} : {myfun 1 2}})

; (check-equal? (top-interp '{local-rec
;                             : square-helper = {lamb : [num n] -> num
;                                                     : {if : {<= n 0}
;                                                           : 0
;                                                           : {+ n {square-helper {- n 2}}}}}
;                             : {locals : {num -> num} square = {lamb : [num n] -> num
;                                                                     : {square-helper {- {* 2 n} 1}}}
;                                       : {square 13}}}) "169")

(check-exn (regexp (regexp-quote "ZODE Lamb return type does not match body"))
           (lambda () 
             (type-check (lambC (list (cons (numT 0) 'x)) (boolT #f) (numC 0)) base-tenv)))

(check-exn (regexp (regexp-quote "ZODE recC body reutrn type invalid"))
           (lambda () (top-interp
                       '{local-rec
                         : myfun = {lamb : [num n] -> num : true}
                         : {myfun}})))

(check-exn (regexp (regexp-quote "ZODE Invalid type"))
           (lambda ()
             (parse '{lamb : [{{num -> 14} {str -> num} -> {bool -> bool}} a] -> num : 8})))

(check-exn (regexp (regexp-quote "ZODE substring, Expected string integer integer, but got:"))
           (lambda () (top-interp
                       '{substring "false" 1.3 1.5})))

(check-equal? (top-interp '{substring "false" 1 3}) "\"al\"")
(check-equal? (top-interp '{num-eq? 3 3}) "true")
(check-equal? (top-interp '{str-eq? "yes" "yes"}) "true")
