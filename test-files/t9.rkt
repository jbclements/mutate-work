;;> Testfail: expected exception with message containing JYSS on test expression: '(top-interp '(proc (x x) go 3))
;;> Testfail: expected exception with message containing JYSS on test expression: '(top-interp '(vars: (z = (proc () go 3)) (z = 9) body: (z)))
;;> Testfail: expected exception with message containing JYSS on test expression: '(parse '(proc ((a : ((num -> 14) (str -> num) -> (bool -> bool)))) go 8))
;;> Testfail: expected exception with message containing JYSS on test expression: '(type-check (parse '(if 4 "abc" "def")) base-tenv)
;;> Testfail: expected exception with message containing JYSS on test expression: '(type-check (parse '(if ((proc () go 13)) 3 4)) base-tenv)
;;> Testfail: expected exception with message containing JYSS on test expression: '(type-check (parse '("abc" 9)) base-tenv)
;;> Testfail: expected exception with message containing JYSS on test expression: '(top-interp '(if false 3 "abc"))
;;> Testfail: while evaluating (top-interp (quote (rec: (fact = (proc ((n : num) (f : (num -> num))) : num go (if (num-eq? n 0) 1 (* n (f (fact (- n 1) f)))))) in (fact 2 (proc ((x : num)) go (- x 10)))))):
;  interp: JYSS t-lookup error! ''rec:
#lang typed/racket
(require typed/rackunit)

;Completion: Fully complete!


; DATA DEFINITIONS
(define-type ExprC (U numC ifC appC idC lamC strC recC))
(struct numC ([n : Real]) #:transparent)
(struct ifC ([a : ExprC] [b : ExprC] [c : ExprC]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lamC ([args : (Listof TBinding)] [body : ExprC]) #:transparent)
(struct strC ([s : String]) #:transparent)
;;> I believe your recC should have more things in it
(struct recC ([proc : lamC] [ret : Ty]) #:transparent)

(define-type Value (U boolV numV strV closV primopV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct strV ([s : String]) #:transparent)
(struct closV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([name : Symbol]) #:transparent)

(define-type Ty (U boolT strT numT funT))
(struct boolT () #:transparent)
(struct strT () #:transparent)
(struct numT () #:transparent)
(struct funT ([argTypes : (Listof Ty)] [resultType : Ty]) #:transparent)

;Env
(struct Binding ((name : Symbol) (val : (Boxof Value))) #:transparent)
(define-type Env (Listof Binding))

;TEnv
(struct TBinding ((name : Symbol) (type : Ty)) #:transparent)
(define-type TEnv (Listof TBinding))

;Base-tenv
(define base-tenv (list
                   (TBinding 'true (boolT))
                   (TBinding 'false (boolT))
                   (TBinding '+ (funT (list (numT) (numT)) (numT)))
                   ;;> why does minus exist? I don't believe that was part of the assignment, but no harm done if you added it for fun
                   (TBinding 'minus (funT (list (numT) (numT)) (numT)))
                   (TBinding '- (funT (list (numT) (numT)) (numT)))
                   (TBinding '* (funT (list (numT) (numT)) (numT)))
                   (TBinding '/ (funT (list (numT) (numT)) (numT)))
                   (TBinding '<= (funT (list (numT) (numT)) (numT)))
                   (TBinding 'equal? (funT (list (numT) (numT)) (numT)))))

;Base-env
;;> missing substring?
(define base-env (list
                  (Binding 'true ((inst box Value) (boolV #t)))
                  (Binding 'false ((inst box Value) (boolV #f)))
                  (Binding '+ ((inst box Value) (primopV '+)))
                  (Binding 'minus ((inst box Value) (primopV '-)))
                  (Binding '- ((inst box Value) (primopV '-)))
                  (Binding '* ((inst box Value) (primopV '*)))
                  (Binding '/ ((inst box Value) (primopV '/)))
                  (Binding '<= ((inst box Value) (primopV '<=)))
                  (Binding 'equal? ((inst box Value) (primopV 'equal?)))))

;top-interp consumes a Sexp and parses + interprets it, outputting an answer
(define (top-interp [s : Sexp]) : String
  (type-check (parse s) base-tenv)
  (serialize (interp (parse s) base-env)))

;get-binding-name consumes a TBinding and returns the name
(define (get-binding-name [b : TBinding]): Symbol
  (match b
    [(TBinding name type) name]))

(check-equal? (get-binding-name (TBinding 'a (numT))) 'a)

;get-binding-type consumes a TBinding and returns the name
(define (get-binding-type [b : TBinding]): Ty
  (match b
    [(TBinding name type) type]))

(check-equal? (get-binding-type (TBinding 'a (numT))) (numT))

;interp consumes an ExprC, interprets it, and returns an answer
(define (interp [a : ExprC] [env : Env]) : Value
  (match a
    [(ifC if left right) (match (interp if env)
                           [(boolV #t) (interp left env)]
                           [(boolV #f) (interp right env)]
                           [other (error "JYSS if not boolean" if)])]
    [(numC n) (numV n)]
    [(strC s) (strV s)]
    [(lamC args body) (closV (for/list ([arg (in-list args)]) (get-binding-name arg)) body env)]
    [(idC (? symbol? s)) (lookup env s)]
    [(appC f a) (local ([define clos (interp f env)])
                  (match clos
                    [(primopV s) (cond
                                   [(equal? (length a) 2) (eval-primop s (interp (car a) env) (interp (last a) env))]
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
                                   [else (error "JYSS primop argument lengths")])]
                    [other (cond
                             [(not (equal? (length (clos-args clos)) (length a)))
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
                              ((error "JYSS appC argument lengths"))]
                             [else (interp
                                    (clos-body clos)
                                    (extend (clos-args clos)
                                            (for/list ([arg (in-list a)])(interp arg env)) (clos-env clos)))])]))]))

;parse-type consumes an s expression, and returns its Type
(define (parse-type [s-exp : Sexp]): Ty
  (match s-exp
    ['str (strT)]
    ['bool (boolT)]
    ['num (numT)]
    [(list inputTypes ... '-> resultType) (funT (for/list ([type (in-list inputTypes)])
                                                  (parse-type (cast type Sexp))) (parse-type (cast resultType Sexp)))]))
(check-equal? (parse-type 'str) (strT))
(check-equal? (parse-type 'bool) (boolT))
(check-equal? (parse-type 'num) (numT))
(check-equal? (parse-type '(num num -> bool)) (funT (list (numT) (numT)) (boolT)))

;extend-tenv consumes a list of TBindings, and an env, and extends the env
(define (extend-tenv [bindings : (Listof TBinding)] [tenv : TEnv]): TEnv
  (match bindings
    ['() tenv]
    [(cons f r) (extend-tenv r (append (list (first bindings)) tenv))]))

(check-equal? (extend-tenv (list (TBinding 'a (numT))) (list)) (list (TBinding 'a (numT))))

;t-lookup consumes an environment and a name and returns the looked up value from the environment
(define (t-lookup [name : Symbol] [env : TEnv]): Ty
  (match env
    ['() (error 'interp "JYSS t-lookup error! ~e" name)]
    [(cons (TBinding fname ftype) r) (cond
                                       [(equal? fname name) ftype]
                                       [else (t-lookup name r)])]))

(check-equal? (t-lookup 'a (list (TBinding 'a (numT)) (TBinding 'b (boolT)))) (numT))
(check-equal? (t-lookup 'b (list (TBinding 'a (numT)) (TBinding 'b (boolT)))) (boolT))
(check-exn (regexp (regexp-quote "JYSS t-lookup error! 'c"))
           (lambda () (t-lookup 'c (list (TBinding 'a (numT)) (TBinding 'b (boolT))))))

;get-input-types consumes a funT and returns a list of input types
(define (get-input-types [f : funT]): (Listof Ty)
  (match f
    [(funT input output) input]))
(check-equal? (get-input-types (funT (list (numT)) (numT))) (list (numT)))

;get-output-type consumes a funT and returns a list of input types
(define (get-output-type [f : funT]): Ty
  (match f
    [(funT input output) output]))
(check-equal? (get-output-type (funT (list (numT)) (numT))) (numT))

;type-check consumes an expression and a type-env and returns a type
(define (type-check [e : ExprC] [tenv : TEnv]): Ty
  (match e
    ; [(recC (lamC args body) ret) (funT (for/list ([arg (in-list args)]) (get-binding-type arg)) ret)]
    [(numC n) (numT)]
    [(strC s) (strT)]
    [(idC name) (t-lookup name tenv)]
    [(ifC a b c) (type-check b tenv)]
    [(appC fun (list args ...)) (cond
                                  ;;> Bug! You can't assume that the return type will be a funT. Consider when it's malformed, check below for an example (labeled problem 1)
                                  [(equal? (get-input-types (cast (type-check fun tenv) funT))
                                           (for/list: : (Listof Ty) ([arg (in-list args)]) (type-check arg tenv)))
                                   ;;> assuming that the output type is funT is dangerous, again...
                                   (get-output-type (cast (type-check fun tenv) funT))]
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
                                  [else (error "JYSS invalid appC types")])]
    [(lamC args body) (funT
                       (for/list ([arg (in-list args)]) (get-binding-type arg))
                       (type-check body (extend-tenv tenv args)))]))


(check-equal? (type-check (numC 1) (list)) (numT))
(check-equal? (type-check (strC "WOW") (list)) (strT))
(check-equal? (type-check (idC 'a) (list (TBinding 'a (numT)))) (numT))
(check-equal? (type-check (ifC (idC 'a) (idC 'b) (idC 'c)) (list (TBinding 'b (numT)))) (numT))
(check-equal? (type-check (appC (idC 'x) (list (idC 'a))) (list
                                                           (TBinding 'a (numT))
                                                           (TBinding 'x (funT (list (numT)) (numT))))) (numT))
(check-exn (regexp (regexp-quote  "invalid appC types"))
           (lambda () (type-check (appC (idC 'x) (list (idC 'a)))
                                  (list (TBinding 'a (numT)) (TBinding 'x (funT (list (strT)) (numT)))))))

(check-equal? (type-check (lamC (list (TBinding 'a (numT))) (idC 'a)) (list)) (funT (list (numT)) (numT)))


;parse-tbinding consumes an s-expression of form [name : Type], and returns a tbinding
(define (parse-tbinding [s-exp : Sexp]): TBinding
  ;;> what happens when the expression is not well formed? You don't handle checking if proc definitions have types in parse, so it errors here
  (match s-exp
    [(list (? symbol? name) ': type) (TBinding name (parse-type type))]))
(check-equal? (parse-tbinding '[name : num]) (TBinding 'name (numT)))

;parse consumes an s expression, parses it, and returns an ExprC
(define (parse [s-exp : Sexp]): ExprC
  (match (desugar s-exp)

    ;;> this matching statement should not be here - proc is defined in the EBNF as not having an explicitly annotated return type
    ;;> oh, unless this is the result of desugaring the rec type... which I believe it is, so nevermind
    [(list 'proc (list params ...) ': retType 'go gos)
     (cond
       [(check-keywords (for/list ([param (in-list params)]) (first params)))
        (error "JYSS keyword recC arguments")]
       [else (recC (lamC (for/list
                             ([param (in-list params)])
                           (parse-tbinding param)) (parse gos))
                   (parse-type retType))])]

    ;;> incorrect match statement, it should be stricter in checking to see if there are types attached to the arguments
    ;;> It should be more inline with what the assignment EBNF states for proc
    [(list 'proc (list params ...) 'go gos)
     (cond
       [(check-keywords (for/list ([param (in-list params)]) (first params)))
        (error "JYSS keyword lamC arguments")]
       ;;> again, you don't know if the definition is well formed, so creating a lamC out of this will cause errors
       [else (lamC (for/list
                       ([param (in-list params)])
                     (parse-tbinding param)) (parse gos))])]
    [(? real? r)   (numC r)]
    [(? string? s) (strC s)]
    [(? symbol? s)   (cond
                       [(check-keywords (list s)) (error 'parse "JYSS Invalid parsing exprc, ~e" s-exp)]
                       [else (idC s)])]
    [(list 'if a b c)  (ifC (parse a) (parse b) (parse c))]
    [(list fn args ...)  (cond
                           [(check-keywords (list fn))
                            (error 'parse "JYSS Invalid parsing exprc, ~e" s-exp)]
                           [else (appC (parse fn) (for/list ([arg (in-list args)])
                                                    (parse arg)))])]
    [other   (error 'parse "JYSS Invalid parsing exprc, ~e" s-exp)]))

;desugar consumes an s exression, and removes the var/body syntax to standard JYSS
(define (desugar [s-exp : Sexp]) : Sexp
  ;;> your desugaring seems to have problems... see how problem #2 (on bottom) is a valid rec that is not desugared at all...
  (match s-exp
    ;;> again, you should be checking to see if the rec is properly formed, following the EBNF
    ;;> certain improperly formed rec's (think no type annotations on the parameters) will still go through here
    [(list 'rec: recs ... 'in (list 'vars: vars ... 'body: body))
     (quasiquote {{proc ,(append (rec-names (cast recs (Listof Sexp)))
                                 (vars-names (cast vars (Listof Sexp)))) go ,body}
                  ,@(append (rec-values (cast recs (Listof Sexp)))
                            (vars-values (cast vars (Listof Sexp))))})]
    [(list 'vars: vars ... 'body: body)
     (quasiquote {{proc ,(vars-names (cast vars (Listof Sexp))) go ,body}
                  ,@(vars-values (cast vars (Listof Sexp)))})]
    [other s-exp]))

;check-keywords consumes a symbol and returns t or f if it is a reserved keyword
(define (check-keywords [args : (Listof Sexp)]) : Boolean
  (match args
    ['() #f]
    [(cons f r)  (cond
                   [(equal? 'if f) #t]
                   [(equal? 'proc f) #t]
                   [(equal? 'go f) #t]
                   [(equal? 'vars: f) #t]
                   [(equal? 'body: f) #t]
                   [else (or #f (check-keywords r))])]))
;define parse-args consumes a list of sexp of [name : type] and returns the types as listof sexp
(define (parse-args [args : Sexp]): (Listof Sexp)
  (for/list ([arg (in-list args)]) (match arg
                                     [(list name ': type) type])))

;rec-name consumes an s-expression of rec and returns the names and types as a listof Sexps
(define (rec-names [s-exps : (Listof Sexp)]) : (Listof Sexp)
  (match s-exps
    ['() s-exps]
    [(cons f r) (cons (match f
                        [(list (? symbol? name) '= (list v ...))
                         (list name ': (match v
                                         [(list 'proc (list args ...) ': type 'go gos)
                                          (append (parse-args args)
                                                  (list '-> type))]))]) (rec-names r))]))


;vars-names consumes an s-expression of vars and returns the names as a listof Sexps
(define (vars-names [s-exps : (Listof Sexp)]) : (Listof Sexp)
  (for/list ([var (in-list s-exps)]) (match var
                                       [(list (? symbol? name) ': type '= v) (list name ': type)])))


;vars-values consumes an s-expression of vars and returns the values as a listof Sexps
(define (vars-values [s-exps : (Listof Sexp)]) : (Listof Sexp)
  (for/list ([var (in-list s-exps)]) (match var
                                       [(list (? symbol? name) ': type '= v) (desugar v)])))

;rec-values consumes an s-expression of vars and returns the values as a listof Sexps
(define (rec-values [s-exps : (Listof Sexp)]) : (Listof Sexp)
  (for/list ([var (in-list s-exps)]) (match var
                                       [(list (? symbol? name) '= v) v])))

;get-val consumes a numV, and returns the primative value
(define (get-val [val : Value]) : Real
  (match val
    [(numV n) n]
    [other (error "JYSS get-val of non numeric value")]))

;eval-primop consumes a symbol and two reals and returns an arithmetic statement corresponding to the correct symbol
(define (eval-primop [s : Symbol] [l : Value] [r : Value]) : Value
  (match s
    ['+  (numV (+ (get-val l) (get-val r)))]
    ['-  (numV (- (get-val l) (get-val r)))]
    ['*  (numV (* (get-val l) (get-val r)))]
    ['<=  (boolV (<= (get-val l) (get-val r)))]
    ['equal? (match (list l r)
               [(list (boolV a) (boolV b)) (boolV (equal? l r))]
               [(list (numV a) (numV b)) (boolV (equal? l r))]
               [(list (strV a) (strV b)) (boolV (equal? l r))]
               [else (boolV #f)])]
    ['/   (cond
            [(equal? r (numV 0))  (error "JYSS Divide by zero")]
            [else (numV (/ (get-val l) (get-val r)))])]
    [other (error 'eval-binop "JYSS Invalid operator ~e" s)]))

;extend consumes a list of symbols and corresponding values, and an env, and extends the env
(define (extend [symbols : (Listof Symbol)] [values : (Listof Value)] [env : Env]): Env
  (match symbols
    ['() env]
    [(cons f r) (extend r (rest values) (append (list (Binding f ((inst box Value) (first values)))) env))]))


;lookup consumes an environment and a name and returns the looked up value from the environment
(define (lookup [env : Env] [name : Symbol]) : Value
  (cond
    [(equal? name 'error) (error "user-error")]
    [else (match env
            ['() (error 'interp "JYSS lookup error! ~e" name)]
            [(cons (Binding fname fval) r) (cond
                                             [(equal? fname name) (unbox fval)]
                                             [else (lookup r name)])])]) )

;serialize consumes a Sexp, serializes it, and returns the string
(define (serialize [v : Value]) : String
  (match v
    [(numV (? real? v)) (~v v)]
    [(boolV (? boolean? v)) (cond
                              [(equal? (~v v) "#t") "true"]
                              [else "false"])]
    [(strV (? string? v)) (~v v)]
    [(closV args body env) "#<procedure>"]
    [(primopV s) "#<primop>"]))

;clos-args consumes a closure and returns the arguments value
(define (clos-args [c : Value]) : (Listof Symbol)
  (match c
    [(closV args body env) args]
    [other (error "JYSS clos-args")]))

;clos-body consumes a closure and returns the body exprC
(define (clos-body [c : Value]) : ExprC
  (match c
    [(closV args body env) body]
    [other (error "JYSS clos-body")]))

;clos-env consume a closure and returns its env
(define (clos-env [c : Value]) : Env
  (match c
    [(closV args body env) env]
    [other (error "JYSS clos-env")]))


;Test Cases
(check-equal? (check-keywords (list 'a 'if)) #t)
(check-equal? (check-keywords (list 'a 'proc)) #t)
(check-equal? (check-keywords (list 'a 'go)) #t)
(check-equal? (check-keywords (list 'body: 'go)) #t)
(check-equal? (check-keywords (list 'vars: 'go)) #t)


(check-equal? (parse 1) (numC 1))
(check-equal? (parse "hello") (strC "hello"))
(check-equal? (parse '{+ 1 x}) (appC (idC '+) (list (numC 1) (idC 'x))))
(check-equal? (parse '{+ 1 {* 3 4}})(appC (idC '+) (list (numC 1) (appC (idC '*) (list (numC 3) (numC 4))))))
(check-equal? (parse '{/ 1 2}) (appC (idC '/) (list (numC 1) (numC 2))))
(check-equal? (parse '{- 1 2}) (appC (idC '-) (list (numC 1) (numC 2))))
(check-equal? (parse '{if true 1 2}) (ifC (idC 'true) (numC 1) (numC 2)))
(check-equal? (parse '{addone x}) (appC (idC 'addone) (list (idC 'x))))
(check-equal? (parse '{proc {[z : num] [y : num]} go {+ z y}}) (lamC (list (TBinding 'z (numT)) (TBinding 'y (numT)))
                                                                     (appC (idC '+) (list (idC 'z) (idC 'y)))))
(check-exn (regexp (regexp-quote "parse: JYSS Invalid parsing exprc, '()"))
           (lambda () (parse {list})))
(check-exn (regexp (regexp-quote "parse: JYSS Invalid parsing exprc, '(proc 3 4 5 5)"))
           (lambda () (parse '(proc 3 4 5 5))))
(check-exn (regexp (regexp-quote "parse: JYSS Invalid parsing exprc, 'if"))
           (lambda () (parse 'if)))

(check-= (get-val (numV 1)) 1 0.01)

(check-= (get-val (eval-primop '+ (numV 1) (numV 1))) 2 0.01)
(check-= (get-val (eval-primop '- (numV 1) (numV 1))) 0 0.01)
(check-= (get-val (eval-primop '* (numV 1) (numV 1))) 1 0.01)
(check-= (get-val (eval-primop '/ (numV 6) (numV 2))) 3 0.01)
(check-equal? (eval-primop '<= (numV 6) (numV 2)) (boolV #f))
(check-equal? (eval-primop 'equal? (numV 2) (numV 2)) (boolV #t))
(check-equal? (eval-primop 'equal? (boolV #f) (boolV #t)) (boolV #f))
(check-equal? (eval-primop 'equal? (strV "s") (strV "s")) (boolV #t))
(check-equal? (eval-primop 'equal? (strV "s") (numV 3)) (boolV #f))
(check-exn (regexp (regexp-quote "JYSS Invalid operator '^"))
           (lambda () (eval-primop '^ (numV 2) (numV 2))))
(check-exn (regexp (regexp-quote  "JYSS Divide by zero"))
           (lambda () (eval-primop '/ (numV 2) (numV 0))))

(check-equal? (extend (list 'c 'd) (list (numV 1) (numV 2)) base-env)
              (append (list (Binding 'd ((inst box Value)(numV 2))) (Binding 'c ((inst box Value)(numV 1)))) base-env))

(check-equal? (lookup (list (Binding 'a ((inst box Value)(numV 1)))
                            (Binding 'b ((inst box Value)(numV 2)))) 'a) (numV 1))
(check-equal? (lookup (list (Binding 'a ((inst box Value)(numV 1)))
                            (Binding 'b ((inst box Value)(numV 2)))) 'b) (numV 2))
(check-exn (regexp (regexp-quote "JYSS lookup error! 'c"))
           (lambda () (lookup (list (Binding 'a ((inst box Value)(numV 1)))
                                    (Binding 'b ((inst box Value)(numV 2)))) 'c)))

(check-equal? (serialize (numV 34)) "34")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (strV "happy")) "\"happy\"")
(check-equal? (serialize (closV (list 'a 'b) (numC 1) base-env)) "#<procedure>")
(check-equal? (serialize (primopV '+)) "#<primop>")

(check-equal? (clos-args (closV (list 'a 'b) (numC 1) base-env)) (list 'a 'b))
(check-exn (regexp (regexp-quote "JYSS clos-args"))
           (lambda () (clos-args (numV 1))))

(check-equal? (clos-body (closV (list 'a 'b) (numC 1) base-env)) (numC 1))
(check-exn (regexp (regexp-quote "JYSS clos-body"))
           (lambda () (clos-body (numV 1))))



(check-= (get-val (interp (appC (idC '+) (list (appC (idC '*) (list (numC 1) (numC 2)))
                                               (numC 1))) base-env)) 3 0.01)
(check-= (get-val (interp (numC -1) base-env)) -1 0.01)
(check-equal? (interp (strC "hello") base-env) (strV "hello"))
(check-= (get-val (interp (appC (idC 'minus) (list (numC 2) (numC 2))) base-env)) 0 0.01)
(check-= (get-val (interp (appC (idC '/) (list (numC 2) (numC 2))) base-env)) 1 0.01)
(check-= (get-val (interp (ifC (idC 'true) (numC 1) (numC 0)) base-env)) 1 0.01)
(check-= (get-val (interp (ifC (idC 'false) (numC 1) (numC 0)) base-env)) 0 0.01)
(check-= (get-val (interp (appC (idC 'fn) (list (numC 1)))
                          (extend (list 'fn) (list (closV (list 'y) (idC 'y) base-env)) base-env))) 1 0.01)
(check-= (get-val (interp (idC 'c) (list (Binding 'c ((inst box Value)(numV 3)))))) 3 0.01)
(check-equal? (interp (lamC (list (TBinding 'a (numT))
                                  (TBinding 'b (numT))) (numC 1)) base-env) (closV (list 'a 'b)
                                                                                   (numC 1) base-env))
(check-exn (regexp (regexp-quote "JYSS primop argument lengths"))
           (lambda () (interp (appC (idC '+) (list (idC 'a))) base-env)))
(check-exn (regexp (regexp-quote "JYSS if not boolean"))
           (lambda () (interp (ifC (idC '+) (numC 1) (numC 0)) base-env)))
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (lookup base-env 'error)))

(check-equal? (top-interp '{vars: [z : num = {+ 9 14}] [y : num = 98] body: {+ z y}}) "121")
(check-exn (regexp (regexp-quote "JYSS invalid appC types"))
           (lambda () (top-interp '((proc () go 9) 17))))
(check-exn (regexp (regexp-quote "JYSS invalid appC types"))
           (lambda () (top-interp '(+ + +))))
(check-equal? (clos-env (closV (list 'a 'b) (numC 1) base-env)) base-env)
(check-exn (regexp (regexp-quote "JYSS clos-env"))
           (lambda () (clos-env (numV 1))))

(check-exn (regexp (regexp-quote "JYSS keyword lamC arguments"))
           (lambda () (parse '(proc (if x) go 3))))

(check-exn (regexp (regexp-quote "JYSS keyword recC arguments"))
           (lambda () (parse '(proc (if x) : num go 3))))

(check-exn (regexp (regexp-quote  "JYSS get-val of non numeric value"))
           (lambda () (get-val (strV "hello"))))



(check-exn (regexp (regexp-quote "JYSS appC argument lengths"))
           (lambda () (interp (appC (idC 'fn) (list (numC 1) (numC 3)))
                              (extend (list 'fn) (list (closV (list 'y) (idC 'y) base-env)) base-env))))


(check-equal?
 (parse
  '{rec:
    [square-helper =
                   {proc {[n : num]} : num go
                         {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}]
    in
    {vars: [square : {num -> num}  =
                   {proc {[n : num]} go {square-helper {- {* 2 n} 1}}}]
           body:
           {square 13}}}) (appC
                           (lamC (list (TBinding 'square-helper (funT (list (numT)) (numT)))
                                       (TBinding 'square (funT (list (numT)) (numT))))
                                 (appC (idC 'square) (list (numC 13))))
                           (list
                            (recC
                             (lamC (list (TBinding 'n (numT)))
                                   (ifC (appC (idC '<=) (list (idC 'n) (numC 0))) (numC 0)
                                        (appC (idC '+)
                                              (list (idC 'n)
                                                    (appC (idC 'square-helper)
                                                          (list (appC (idC '-)
                                                                      (list (idC 'n) (numC 2)))))))))
                             (numT))
                            (lamC (list (TBinding 'n (numT)))
                                  (appC (idC 'square-helper)
                                        (list (appC (idC '-)
                                                    (list (appC (idC '*)
                                                                (list (numC 2) (idC 'n)))
                                                          (numC 1)))))))))

;;> problem 1!
;;> (type-check (parse '{vars: [x : num = 3] body: {x 4 5}}) base-tenv)

;;> problem 2!
;;> desugaring seems to do nothing here:
;;>(desugar '(rec: (fact = (proc ((n : num) (f : (num -> num))) : num go (if (num-eq? n 0) 1 (* n (f (fact (- n 1) f)))))) in (fact 2 (proc ((x : num)) go (- x 10)))))
