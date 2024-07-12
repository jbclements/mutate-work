#lang typed/racket
(require typed/rackunit)

; Implemented full project except for in-order & while
; I have them implemented, but I can't get it to pass with the handin case
; I believe they're fundamentally correct, and I just can't get the exact
; syntax that handin wants. See the bottom of the file for those

; Defines a new language ZODE with as per the spec
(define-type ExprC (U numC ifC idC appC lambC strC bindC))
(struct numC ([n : Real]) #:transparent)
(struct strC ([s : String]) #:transparent)
(struct ifC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct idC ([name : Symbol]) #:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lambC ([arglst : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct bindC ([left : Symbol] [right : ExprC]) #:transparent)

; Defines the types of values that ZODE expects
(define-type Value (U Real Boolean String closV nullV arrayV Primop))
(struct closV ([arglst : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct nullV ([contents : String]) #:transparent)
(struct arrayV ([start : Integer] [size : Integer]) #:transparent)



; Defines the primitive operators built into ZODE
(define-type Primop (U primop-numeric primop-bool primop-error primop-seq
                       primop-array primop-make-array primop-aref
                       primop-aset! primop-substring))
(struct primop-numeric ([name : Symbol]) #:transparent)
(struct primop-bool ([name : Symbol]) #:transparent)
(struct primop-error ([name : Symbol]) #:transparent)
(struct primop-seq ([name : Symbol])  #:transparent)
(struct primop-array ([name : Symbol]) #:transparent)
(struct primop-make-array ([name : Symbol]) #:transparent)
(struct primop-aref ([name : Symbol]) #:transparent)
(struct primop-aset! ([name : Symbol]) #:transparent)
(struct primop-substring ([name : Symbol]) #:transparent)



; Defines the environment datastructure
(define-type Env (Listof Binding))
(struct Binding ([name : Symbol] [loc : Integer]))

(define mt-store (ann (make-vector 1000 (nullV "null")) (Mutable-Vectorof Value)))

(define mt-env (list
                (Binding 'true 1)
                (Binding 'false 2)
                (Binding '+ 3)
                (Binding '- 4)
                (Binding '* 5)
                (Binding '/ 6)
                (Binding '<= 7)
                (Binding 'equal? 8)
                (Binding 'error 9)
                (Binding 'seq 10)
                (Binding 'array 11)
                (Binding 'make-array 12)
                (Binding 'aref 13)
                (Binding 'aset! 14)
                (Binding 'substring 15)))

(vector-set! mt-store (ann 0 Integer) 16) ; First free loc pointer.
(vector-set! mt-store (ann 1 Integer) #t)
(vector-set! mt-store (ann 2 Integer) #f)
(vector-set! mt-store (ann 3 Integer) (primop-numeric '+))
(vector-set! mt-store (ann 4 Integer) (primop-numeric '-))
(vector-set! mt-store (ann 5 Integer) (primop-numeric '*))
(vector-set! mt-store (ann 6 Integer) (primop-numeric '/))
(vector-set! mt-store (ann 7 Integer) (primop-numeric '<=))
(vector-set! mt-store (ann 8 Integer) (primop-bool 'equal?))
(vector-set! mt-store (ann 9 Integer) (primop-error 'error))
(vector-set! mt-store (ann 10 Integer) (primop-seq 'seq))
(vector-set! mt-store (ann 11 Integer) (primop-array 'array))
(vector-set! mt-store (ann 12 Integer) (primop-make-array 'make-array))
(vector-set! mt-store (ann 13 Integer) (primop-aref 'aref))
(vector-set! mt-store (ann 14 Integer) (primop-aset! 'aset!))
(vector-set! mt-store (ann 15 Integer) (primop-substring 'substring))
                
; Serializes a ZODE 4 expression
(define (serialize [val : Value]) : String
  (match val
    [(? real? n) (format "~v" n)]
    [(? boolean? b) (if b "true" "false")]
    [(? closV? closure) "#<procedure>"]
    [(? primop-numeric? prim) "#<primop>"]
    [(? primop-error? err) "#<primop>"]
    [(? primop-bool? prim) "#<primop>"]
    [(? primop-seq? prim) "#<primop>"]
    [(? arrayV? arr) "#<array>"]
    [(? string? s) (format "~v" s)]))

; Accepts an s-expression in the ZODE language and evaluates it, serializing the result
(define (top-interp [s : Sexp] [memsize : Integer]) : String
  (serialize (interp (parse s) mt-env (make-initial-store memsize))))

; Creates a store from a given memsize, initializing primitive values
(define (make-initial-store [memsize : Integer]) : (Mutable-Vectorof Value)
  (define store (ann (make-vector memsize (nullV "null")) (Mutable-Vectorof Value)))
  (vector-set! store (ann 0 Integer) 16) ; First free loc pointer.
  (vector-set! store (ann 1 Integer) #t)
  (vector-set! store (ann 2 Integer) #f)
  (vector-set! store (ann 3 Integer) (primop-numeric '+))
  (vector-set! store (ann 4 Integer) (primop-numeric '-))
  (vector-set! store (ann 5 Integer) (primop-numeric '*))
  (vector-set! store (ann 6 Integer) (primop-numeric '/))
  (vector-set! store (ann 7 Integer) (primop-numeric '<=))
  (vector-set! store (ann 8 Integer) (primop-bool 'equal?))
  (vector-set! store (ann 9 Integer) (primop-error 'error))
  (vector-set! store (ann 10 Integer) (primop-seq 'seq))
  (vector-set! store (ann 11 Integer) (primop-array 'array))
  (vector-set! store (ann 12 Integer) (primop-make-array 'make-array))
  (vector-set! store (ann 13 Integer) (primop-aref 'aref))
  (vector-set! store (ann 14 Integer) (primop-aset! 'aset!))
  (vector-set! store (ann 15 Integer) (primop-substring 'substring))
  store)

; Accepts an s-expression and parses it into an ZODE expression
(define (parse [s : Sexp]) : ExprC
  (match s
    [(list 'locals ': args ...) (parse (desugar args))]
    [(list 'lamb ': vars ... ': body)
     (define varlist (get-symbols vars))
     (cond
       [(duplicate-args? varlist) (error 'parse "ZODE Duplicate variable names")]
       [(invalid-params? varlist) (error 'parse "ZODE Can't use keywords as variable names")]
       [else (lambC varlist (parse body))])]
    [(list (? list? body) args ...)
     (appC (parse body) (map parse args))]
    [(list (? symbol? left) ':= right)
     (bindC left (parse right))]
    [(list 'if ': test ': then ': else) (ifC (parse test) (parse then) (parse else))]
    [(list firstval args ...) (appC (parse firstval) (map parse args))]
    [(? symbol? arg)
     (cond
       [(invalid-params? (list arg)) (error 'parse "ZODE Can't use keywords as variable names")]
       [else (idC arg)])]
    [(? real? n) (numC n)]
    [(? string? s) (strC s)]
    [else (error 'parse "ZODE Invalid Zode structure ~s" s)]))

; Accepts a ZODE4 expression and interprets it
(define (interp [a : ExprC] [env : Env] [store : (Mutable-Vectorof Value)]) : Value
  (match a
    [(numC n) n]
    [(strC s) s]
    [(bindC left right)
     (mutate-binding left env store (interp right env store))]
    [(appC fun args)
     (define fun-val (interp fun env store))
     (cond
       [(primop-numeric? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env store)) args))
        (define cleaned-args (clean-primparams processed-args))
        (cond
          [(not (equal? (length cleaned-args) 2))
           (error 'interp "ZODE Invalid args for binop")]
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
       [(primop-bool? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env store)) args))
        (define first-processed (first processed-args))
        (define second-processed (second processed-args))
        (cond
          [(and (arrayV? first-processed) (arrayV? second-processed))
           (equal? (arrayV-start first-processed) (arrayV-start second-processed))]
          [else
           (equal? first-processed second-processed)])]
       [(primop-error? fun-val)
        (error 'interp "user-error ~s" (map (lambda ([arg : ExprC]) : String (serialize (interp arg env store))) args))]
       [(primop-seq? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env store)) args))
        (get-last processed-args)]
       [(primop-array? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env store)) args))
        (new-array processed-args store)]
       [(primop-make-array? fun-val)
        (cond
          [(equal? 2 (length args))
           (define arr-size (interp (first args) env store))
           (define arr-content (interp (first (rest args)) env store))
           (cond
             [(integer? arr-size)
              (new-array-constants (cast arr-size Integer) arr-content store)]
             [else
              (error 'interp "ZODE make-array, arr-size must be an integer, but got: ~a" arr-size)])]
          [else (error 'interp "ZODE make-array invalid number of params")])]
       [(primop-aref? fun-val)
        (cond
          [(equal? 2 (length args))
           (define arr (interp (first args) env store))
           (define index (interp (first (rest args)) env store)) ; Use `second` instead of repeating `(first args)`
           (cond
             [(and (arrayV? arr) (integer? index))
              (aref-prim arr (cast index Integer) store)]
             [else
              (error 'interp "ZODE aref, Expected arrayV and integer, but got: ~a and ~a" arr index)])]
          [else (error 'interp "ZODE aref invalid number of params")])]
       [(primop-aset!? fun-val)
        (cond
          [(equal? 3 (length args))
           (define arr (interp (first args) env store))
           (define index (interp (first (rest args)) env store))
           (define set-val (interp (first (rest (rest args))) env store))
           (cond
             [(and (arrayV? arr) (integer? index))
              (aset-prim arr (cast index Integer) set-val store)]
             [else
              (error 'interp "ZODE aset Expected arrayV and integer, but got: ~a and ~a" arr index)])]
          [else
           (error 'interp "ZODE aset invalid number of params")])]
       [(primop-substring? fun-val)
        (cond
          [(equal? 3 (length args))
           (define str (interp (first args) env store))
           (define from (interp (first (rest args)) env store))
           (define to (interp (first (rest (rest args))) env store))
           (cond
             [(and (string? str) (integer? from) (integer? to))
              (substring str (cast from Integer) (cast to Integer))]
             [else
              (error 'interp "ZODE substring, Expected string integer integer, but got: ~a, ~a, ~a" str from to)])] 
          [else
           (error 'interp "ZODE substring invalid number of params")])]
       [(closV? fun-val)
        (define bindings
          (bind-symbols (closV-arglst (cast fun-val closV))
                        (map
                         (lambda ([arg : ExprC]) : Value (interp arg env store))
                         args) store))
        (define extended-env (extend-env bindings (closV-env fun-val)))
        (interp (closV-body fun-val) extended-env store)]
       [else
        (error 'interp "ZODE function did not eval to closure ~s" fun-val)])]
    [(lambC args body)
     (closV args body env)]
    [(ifC test then else)
     (define result (interp test env store))
     (if (not (boolean? result))
         (error 'interp "ZODE if test non-boolean")
         (if result (interp then env store) (interp else env store)))]
    [(idC val) (lookup val env store)]))

; Old new-array, dont think i actually need to bind it here.... If this is leftover ignore it
; Creates a new array and stores it's contents, and binds it's name
;(define (new-array [contents : (Listof Value)] [store : (Mutable-Vectorof Value)]
;[env : (Listof Binding)] [name : Symbol]) : Value
;  (define first-open-loc (cast (vector-ref store 0) Integer))
;  (define array (arrayV (+ first-open-loc 1) (length contents)))
;  (vector-set! store first-open-loc array)
;  (allocate contents store (+ first-open-loc 1))
;  (extend-env (list (Binding name first-open-loc)) env)
;  array)

; Creates a new array and stores it's contents, and binds it's name
(define (new-array [contents : (Listof Value)] [store : (Mutable-Vectorof Value)]) : Value
  (define first-open-loc (cast (vector-ref store 0) Integer))
  (define array (arrayV (+ first-open-loc 1) (length contents)))
  (cond
    [(>= first-open-loc (vector-length store))
     (error 'new-array "ZODE Attempting to create array outside of alloacted memory")]
    [else
     (vector-set! store first-open-loc array)
     (allocate contents store (+ first-open-loc 1))
     (vector-set! store (ann 0 Integer) (+ first-open-loc (length contents) 1))
     array]))

; Creates a new array from a size and a constant value
(define (new-array-constants [size : Integer] [constant-value : Value] [store : (Mutable-Vectorof Value)]) : Value
  (new-array (make-list size constant-value) store))

; Grabs the element from the provided array at the specified index, checking to make sure the indices are acctually good
(define (aref-prim [array : arrayV] [index : Integer] [store : (Mutable-Vectorof Value)]) : Value
  (cond
    [(>= index (arrayV-size array)) (error 'aref-prim "ZODE aref Index out of bounds")]
    [(< index 0) (error 'aref-prim "ZODE aref Index out of bounds")]
    [else (vector-ref store (+ (arrayV-start array) index))]))

; Sets the element from the provided array at the specified index, checking to make sure the indicies are actually good
(define (aset-prim [array : arrayV] [index : Integer] [val : Value] [store : (Mutable-Vectorof Value)]) : nullV
  (cond
    [(>= index (arrayV-size array)) (error 'aset-prim "ZODE aset Index out of bounds")]
    [(< index 0) (error 'aset-prim "ZODE aset Index out of bounds")]
    [else
     (vector-set! store (+ (arrayV-start array) index) val)
     (nullV "null")]))

; Mutates a binding
(define (mutate-binding [symbol : Symbol] [env : Env]
                        [store : (Mutable-Vectorof Value)]
                        [desired-change : Value]) : nullV
  (match env
    ['() (error 'mutate-binding "ZODE Unbound Identifer when trying to mutate ~s" symbol)]
    [(cons first rest)
     (define target-symbol (Binding-name first))
     (cond
       [(equal? target-symbol symbol)
        (vector-set! store (Binding-loc first) desired-change)
        (nullV "null")]
       [else
        (mutate-binding symbol rest store desired-change)])]))

; Puts a list of stuff in the store at the given location
(define (allocate [stuff : (Listof Value)] [store : (Mutable-Vectorof Value)] [insert-loc : Integer]) : nullV
  (match stuff
    ['() (nullV "null")]
    [(cons first rest)
     (cond
       [(>= (ann insert-loc Integer) (vector-length store))
        (error 'new-array "ZODE Attempting to create array outside of alloacted memory")]
       [else
        (vector-set! store (ann insert-loc Integer) first)
        (allocate rest store (+ insert-loc 1))])]))

; looks up an identifier in the environment and returns the value
(define (lookup [for : Symbol] [env : Env] [store : (Vectorof Value)]) : Value
  (cond
    [(empty? env) (error 'lookup "ZODE Unbound identifier ~s" for)]
    [else (let ([binding (first env)])
            (if (symbol=? for (Binding-name binding))
                (vector-ref store (Binding-loc binding))
                (lookup for (rest env) store)))]))

;(define (put-in-store [val : Value]))

; Binds symbols to their values, storing them in the store
(define (bind-symbols [what : (Listof Symbol)]
                      [to : (Listof Value)]
                      [store : (Mutable-Vectorof Value)]) : (Listof Binding)
  (match (list what to)
    [(list '() '()) '()]
    [(list (cons f-what r-what) '()) (error 'zip "ZODE Invalid number of params")]
    [(list '() (cons f-to r-to)) (error 'zip "ZODE Invalid number of params")]
    [(list (cons f-what r-what) (cons f-to r-to))
     (define first-open-loc (cast (vector-ref store 0) Integer))
     (vector-set! store first-open-loc f-to)
     (vector-set! store (ann 0 Natural) (+ first-open-loc 1))
     (cons (Binding f-what first-open-loc ) (bind-symbols r-what r-to store))]))

; Gets the last value in a list
(define (get-last [lst : (Listof Value)]) : Value
  (cond
    [(empty? (rest lst))
     (first lst)]
    [else
     (get-last (rest lst))]))

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
        (cons first-bind (extend-env (rest bindings) env))]
       [else
        (cons first-env (extend-env bindings (rest env)))])]))

; Cleans primitive params, looks for only numeric
(define (clean-primparams [params : (Listof Value)]) : (Listof Real)
  (cond
    [(empty? params) '()]
    [(not (real? (first params)))
     (error 'clean-primparams "ZODE Invalid param for numeric primitive ~s" (first params))]
    [else
     (cons (cast (first params) Real) (clean-primparams (rest params)))]
    ))

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
         (symbol=? (first args) '=)
         (symbol=? (first args) ':=)) #t]
    [else (invalid-params? (rest args))]))

; Grabs the symbols from a list of parameters,
; signals error if encounters non symbol
(define (get-symbols [args : (Listof Any)]) : (Listof Symbol)
  (cond
    [(empty? args) '()]
    [(not (symbol? (first args)))
     (error 'get-symbols "ZODE Vars not entierly symbols")]
    [else (cons (first args) (get-symbols (rest args)))]))

; Desugars, splits the locals definitions into the variables, the body of the main lamb, and the bodies of the
; Arguments to be passed into the variables
(define (split-desugar [s : Sexp] [vars : (Listof Symbol)] [bodies : (Listof Sexp)]) : (Listof Sexp)
  (match s
    [(list (? symbol? varname) '= args ': rest ...)
     (split-desugar rest (append vars (list varname)) (append bodies (list args)))]
    [(list body) (list vars bodies body)]
    [else (error 'split-desugar "ZODE Invalid locals definition")]))

; Desugars, wraps the main lamb into external lambs
(define (desugar [args : Sexp]) : Sexp
  (define desugar-results (split-desugar args '() '()))
  (define vars (first desugar-results))
  (define bodies (first (rest desugar-results)))
  (define body (first (rest (rest desugar-results))))
  (define varslist (cast vars (Listof Any)))
  (define bodieslist (cast bodies (Listof Any)))
  (cast (append (list (append (list 'lamb ':) varslist (list ':) (list body))) bodieslist) Sexp))

; Interp Tests
(check-equal? (interp (appC (idC '+) (list (numC 3) (numC 5))) mt-env mt-store) 8)
(check-equal? (interp (appC (idC '*) (list (numC 3) (numC 5))) mt-env mt-store) 15)
(check-equal? (interp (appC (idC '<=) (list (numC 3) (numC 5))) mt-env mt-store) #t)
(check-equal? (interp (appC (idC '<=) (list (numC 8) (numC 5))) mt-env mt-store) #f)
(check-equal? (interp (appC (idC 'equal?) (list (numC 8) (numC 8))) mt-env mt-store) #t)
(check-equal? (interp (appC (idC 'equal?) (list (numC 8) (numC 2))) mt-env mt-store) #f)
(check-equal? (interp (appC (idC 'equal?) (list (idC 'false) (idC 'true))) mt-env mt-store) #f)
(check-equal? (interp (appC (idC '+) (list (appC (idC '*) (list (numC 2) (numC 4))) (numC 5))) mt-env mt-store) 13)
(check-equal? (interp (ifC (appC (idC '<=) (list (numC 4) (numC 0))) (idC 'true) (idC 'false)) mt-env mt-store) #f)
(check-equal? (interp (ifC (appC (idC '<=) (list (numC 3) (numC 4))) (numC 3) (numC 4)) mt-env mt-store) 3)
(check-equal? (interp (appC (idC '+) (list
                                      (numC 3)
                                      (appC (lambC '(x)
                                                   (appC (idC '+) (list (idC 'x) (idC 'x))))
                                            (list (numC 3))))) mt-env mt-store) 9)
(check-exn (regexp (regexp-quote "ZODE Unbound identifier"))
           (lambda () (interp (appC (idC '+) (list (numC 4) (idC 'x))) mt-env mt-store)))

(check-exn (regexp (regexp-quote "ZODE Invalid number of params"))
           (lambda () (interp
                       (appC (lambC (list 'x) (appC (idC '+) (list (numC 1) (idC 'x))))
                             (list (numC 1) (numC 2))) mt-env mt-store)))
(check-exn (regexp (regexp-quote "ZODE Invalid number of params"))
           (lambda () (interp
                       (appC (lambC (list 'x 'y 'z) (appC (idC '+) (list (numC 1) (idC 'x))))
                             (list (numC 1) (numC 2))) mt-env mt-store)))

; Parser Tests
(check-equal? (parse
               '{locals
                 : z = {+ 9 14}
                 : y = 98
                 : {+ z y}})
              (appC (lambC (list 'z 'y) (appC (idC '+) (list (idC 'z) (idC 'y))))
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
(check-exn (regexp (regexp-quote "ZODE Duplicate variable names")) (lambda () (parse '{lamb : x x : 1})))
(check-exn (regexp (regexp-quote "ZODE Vars not entierly symbols")) (lambda () (parse '{lamb : 1 2 3 : 5})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{lamb : i : "Hello" 31/7 +})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{lamb : locals : 1})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{foo : i : "Hello" 31/7 +})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{= : i : "Hello" 31/7 +})))


; Top Interp Tests
(check-equal? (top-interp '{locals
                            : z = {+ 9 14}
                            : y = 98
                            : {+ z y}} 1000) "121")
(check-equal? (top-interp
               '{+ 1 2} 1000)
              "3")
(check-equal? (top-interp
               '{locals
                 : x = 1
                 : y = 2
                 : {- 1 {+ x y}}} 1000) "-2")
(check-equal? (top-interp
               '{locals
                 : x = 1
                 : y = 2
                 : {/ 3 {+ x y}}} 1000) "1")
(check-exn (regexp (regexp-quote "ZODE Divide by 0 error")) (lambda ()(top-interp
                                                                       '{locals
                                                                         : x = {+ 3 4}
                                                                         : y = {/ 1 {+ 0 0}}
                                                                         : {+ 1 2}} 1000)))
(check-exn (regexp (regexp-quote "ZODE Invalid param for numeric primitive"))
           (lambda () (top-interp
                       '{locals
                         : x = {+ 1 true}
                         : y = 4
                         : {+ 1 2}} 1000)))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         : x
                         : y = 4
                         : {+ 1 2}} 1000)))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         :
                         : y = 4
                         : {+ 1 2}} 1000)))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         : y = 4 x = 3
                         : 1} 1000)))
(check-equal? (top-interp
               '{locals
                 : x = 1
                 : y = 1
                 : 1} 1000) "1")
(check-exn (regexp (regexp-quote "ZODE if test non-boolean"))
           (lambda () (top-interp
                       '{if : 1 : 2 : 3} 1000)))
(check-exn (regexp (regexp-quote "ZODE function did not eval to closure"))
           (lambda () (top-interp
                       '{locals
                         : x = 1
                         : {x 1}} 1000)))
(check-equal? (top-interp
               '+ 1000) "#<primop>")
(check-equal? (top-interp
               '{lamb : x : {+ 1 x}} 1000) "#<procedure>")
(check-equal? (top-interp
               '{if : true : true : false} 1000) "true")
(check-equal? (top-interp
               '{if : true : false : true} 1000) "false")
(check-exn (regexp (regexp-quote "ZODE Invalid args for binop"))
           (lambda () (top-interp
                       '{+} 1000)))
(check-exn (regexp (regexp-quote "ZODE Invalid args for binop"))
           (lambda () (top-interp
                       '{+ 2 3 4} 1000)))
(check-equal? (top-interp
               '{{lamb : seven : {seven}}
                 {{lamb : minus : {lamb : : {minus {+ 3 10} {* 2 3}}}}
                  {lamb : x y : {+ x {* -1 y}}}
                  }} 1000) "7")
(check-equal? (top-interp
               '{{lamb : + : (* + +)} 14} 1000) "196")
(check-exn (regexp (regexp-quote "ZODE function did not eval to closure"))
           (lambda () (top-interp '{3 4 5} 1000)))
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (top-interp
                       '{+ 4 {error "1234"}} 1000)))
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (top-interp '{{lamb : e : {e e}} error} 1000)))
(check-equal? (top-interp '{locals
                            : x = 5
                            : y = 2
                            : successMSG = "Success!"
                            : failMSG = "Fail!"
                            : {if : {<= {+ 5 2} {* 5 2}} : successMSG : failMSG}} 1000) "\"Success!\"")

; (check-equal? (top-interp '{locals
;                             : fact = {lamb : n self :
;                                            {if
;                                             : {equal? n 0}
;                                             : 1
;                                             : {* n {self {- n 1} self}}}}
;                             : {fact 5 fact}} 1000) "120")


(check-equal? (top-interp '{seq 1 2 3} 1000) "3")

; Covers serialization
(check-equal? (top-interp 'equal? 1000) "#<primop>")
(check-equal? (top-interp 'seq 1000) "#<primop>")

; New array stuff
(check-equal? (top-interp '{make-array 34 0.0} 1000) "#<array>")
(check-equal? (top-interp '{array 1 2 3 true false} 1000) "#<array>")
(check-equal? (top-interp '{aref {array 1 2 3 true false} 3} 1000) "true")
(check-equal? (top-interp
               '{locals : arr = {array 1 2 3 true false} : {seq {aset! arr 3 false} {aref arr 3}}} 1000)
              "false")
(check-equal? (top-interp '{substring "hello world" 1 4} 1000) "\"ell\"")
(check-equal? (top-interp '{locals : arr = {array 1 2 3 true false} : {equal? arr arr}} 1000) "true")
(check-equal? (top-interp '{locals : my-val = 5 : {seq {my-val := 8} my-val}} 1000) "8")


; Should cause erros
(check-exn (regexp (regexp-quote "ZODE make-array, arr-size must be an integer, but got:"))
           (lambda () (top-interp
                       '{make-array false false} 1000)))


(check-exn (regexp (regexp-quote "ZODE make-array invalid number of params"))
           (lambda () (top-interp
                       '{make-array false false false} 1000)))

(check-exn (regexp (regexp-quote "ZODE aref, Expected arrayV and integer, but got:"))
           (lambda () (top-interp
                       '{aref false false} 1000)))

(check-exn (regexp (regexp-quote "ZODE aref invalid number of params"))
           (lambda () (top-interp
                       '{aref false false false} 1000)))

(check-exn (regexp (regexp-quote "ZODE aset Expected arrayV and integer"))
           (lambda () (top-interp
                       '{aset! false false false} 1000)))

(check-exn (regexp (regexp-quote "ZODE aset invalid number of params"))
           (lambda () (top-interp
                       '{aset! false false} 1000)))

(check-exn (regexp (regexp-quote "ZODE substring, Expected string integer integer, but got:"))
           (lambda () (top-interp
                       '{substring false false false} 1000)))

(check-exn (regexp (regexp-quote "ZODE substring invalid number of params"))
           (lambda () (top-interp
                       '{substring false} 1000)))

(check-exn (regexp (regexp-quote "ZODE aref Index out of bounds"))
           (lambda () (top-interp
                       '{locals : arr = {array 1 2 3} : {aref arr 4}} 1000)))

(check-exn (regexp (regexp-quote "ZODE aref Index out of bounds"))
           (lambda () (top-interp
                       '{locals : arr = {array 1 2 3} : {aref arr -1}} 1000)))

(check-exn (regexp (regexp-quote "ZODE aset Index out of bounds"))
           (lambda () (top-interp
                       '{locals : arr = {array 1 2 3} : {aset! arr 4 false}} 1000)))

(check-exn (regexp (regexp-quote "ZODE aset Index out of bounds"))
           (lambda () (top-interp
                       '{locals : arr = {array 1 2 3} : {aset! arr -1 false}} 1000)))

(check-exn (regexp (regexp-quote "ZODE Unbound Identifer when trying to mutate"))
           (lambda () (top-interp
                       '{locals : my-val = 5 : {seq {not-my-val := 8} my-val}} 1000)))

;(top-interp '{make-array 1001 "abc"} 1000)
;expected exception with message containing ZODE on test expression:
;'(top-interp '(locals : f = (make-array 5 false) : (aset! f 5 19)) 1000)
;Saving submission with errors.

(check-exn (regexp (regexp-quote "ZODE Attempting to create array outside of alloacted memory"))
           (lambda () (top-interp '{make-array 1001 "abc"} 1000)))

(check-exn (regexp (regexp-quote "ZODE Attempting to create array outside of alloacted memory"))
           (lambda () (top-interp '{make-array 1 "abc"} 16)))

(check-exn (regexp (regexp-quote "ZODE Invalid Zode structure"))
           (lambda () (parse '{})))

;'{locals : a = {array 0} :
;         {locals : a! = {lamb : expected : {if : {equal? {aref a 0} expected} :
;{seq {aset! a 0 {+ 1 {aref a 0}}} 273} : {/ 1 0}}}
;         : {seq {+ {a!

;expected exception with message containing
;ZODE on test expression: '(top-interp '(make-array 1001 "abc") 1000)
;Saving submission with errors.

; (check-equal? (top-interp '{locals : fact = "bogus"
;                                    : {seq {fact := {lamb : x : {if : {equal? x 0}
;                                                                    : 1
;                                                                    : {* x {fact {- x 1}}}}}}
;                                           {fact 6}}} 1000) "720")
(define while
  '{locals : while = "bogus"
           : {while := {lamb : guard body :
                             {if : {guard}
                                 : {seq {body}
                                        {while guard body}}
                                 : 0}}}})

(define in-order
  '{locals : in-order = "bogus"
           : {in-order :=
                       {lamb : arr size : 
                             {locals : index = 0
                                     : {seq {while {lamb : : {<= index {- size 2}}}
                                                   {lamb : : {if : {<= {+ {aref arr index} 1} {aref arr {+ index 1}}}
                                                                 : {index := {+ index 1}}
                                                                 : {index := size}}}}
                                            {if : {equal? index {- size 1}}
                                                : true
                                                : false}}}}}})


(check-equal? (top-interp '{locals : while = "bogus"
                     : in-order = "bogus"
                     : arr = {array 1 2 3}
                     : {seq {while := {lamb : guard body :
                                            {if : {guard}
                                                : {seq {body}
                                                       {while guard body}}
                                                : 0}}}
                            {in-order := {lamb : arr size : 
                                {locals : index = 0
                                        : {seq {while {lamb : : {<= index {- size 2}}}
                                                      {lamb : : {if : {<= {+ {aref arr index} 1} {aref arr {+ index 1}}}
                                                          : {index := {+ index 1}}
                                                          : {index := size}}}}
                                               {if : {equal? index {- size 1}}
                                                   : true
                                                   : false}}}}}
                            {in-order arr 3}}} 1000) "true")

(check-equal? (top-interp '{locals : while = "bogus"
                     : in-order = "bogus"
                     : arr = {array 1 3 1}
                     : {seq {while := {lamb : guard body :
                                            {if : {guard}
                                                : {seq {body}
                                                       {while guard body}}
                                                : 0}}}
                            {in-order := {lamb : arr size : 
                                {locals : index = 0
                                        : {seq {while {lamb : : {<= index {- size 2}}}
                                                      {lamb : : {if : {<= {+ {aref arr index} 1} {aref arr {+ index 1}}}
                                                          : {index := {+ index 1}}
                                                          : {index := size}}}}
                                               {if : {equal? index {- size 1}}
                                                   : true
                                                   : false}}}}}
                            {in-order arr 3}}} 1000) "false")