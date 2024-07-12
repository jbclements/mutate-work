#lang typed/racket
(require typed/rackunit)

;;> eyeball: 5/6, generally good; see comments below.

(define-type-alias Enviroment (Listof Binding))
(struct Binding [(name : Symbol) (val : Value)] #:transparent)


;; no, Binop should not be in this union:
(define-type ExprC (U NumC Binop CondC lamC IdC AppC StringC))
(struct IdC ([s : Symbol]))
(struct StringC ([s : String]))
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]))
(struct CondC ([v : ExprC] [t : ExprC] [e : ExprC]))
(struct NumC ([n : Real]))
(struct Binop ([op : Sexp] [l : ExprC] [r : ExprC]))
(struct lamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Enviroment]) #:transparent)
(struct PrimopV ([name : Symbol]) #:transparent)
(define-type Value (U Real Boolean ClosV PrimopV String))
;reserved words
(define top-level-env : Enviroment (list (Binding 'true #t)
                                         (Binding 'false #f)
                                         (Binding '+ (PrimopV '+))
                                         (Binding '- (PrimopV '-))
                                         (Binding '* (PrimopV '*))
                                         (Binding '/ (PrimopV '/))
                                         (Binding '<= (PrimopV '<=))
                                         (Binding 'equal? (PrimopV 'equal?))))
;convert output into a string
(define (serialize [v : Value]) : String
  (match v
    [(? real? v) (~r v)]
    [(? boolean? v) (match (cast v Boolean)
                      [#t "true"]
                      [#f "false"])]
    [(? string? v) (string-append (string-append "\""  v) "\"")]
    [(ClosV args body env) "#<procedure>"]
    [(PrimopV name) "#<primop>"]))

(define reserved : (Immutable-HashTable Symbol Boolean)
  (hash
  'var #t
  'if #t
  '-> #t
  '= #t))

;lookup a primitive operator and evaluate
(define (do-primop [op : Symbol] [args : (Listof Value)]) : Value
  (match op
    ;;> some abstraction here would be nice:
    ['+ #:when (equal? (length args) 2) ((lambda ([x : Value] [y : Value]) (cond
                                         [(and (real? x) (real? y)) (+ x y )]
                                         [else (error "ZNQR: invalid arguments to + " x y)]))
                                         (first args) (second args))]
    ['- #:when (equal? (length args) 2) ((lambda ([x : Value] [y : Value]) (cond
                                         [(and (real? x) (real? y)) (- x y )]
                                         [else (error "ZNQR: invalid arguments to - " x y)]))
                                         (first args) (second args))]
    ['* #:when (equal? (length args) 2) ((lambda ([x : Value] [y : Value]) (cond
                                         [(and (real? x) (real? y)) (* x y )]
                                         [else (error "ZNQR: invalid arguments to * " x y)]))
                                         (first args) (second args))]
    ['/ #:when (equal? (length args) 2) ((lambda ([x : Value] [y : Value]) (cond
                                         [(and (real? x) (real? y)) (match y
                                                                      [0 (error "ZNQR: Divide by zero error")]
                                                                      [_ (/ x y)])]
                                         [else (error "ZNQR: invalid arguments to / " x y)]))
                                         (first args) (second args))]
    ['<= #:when (equal? (length args) 2) ((lambda ([x : Value] [y : Value]) (cond
                                         [(and (real? x) (real? y)) (<= x y)]
                                         [else (error "ZNQR: invalid arguments to <= " x y)]))
                                          (first args) (second args))]
    ['equal? #:when (equal? (length args) 2) ((lambda ([x : Value] [y : Value])
                                                (match x
                                                  [(? real? n) #:when (real? y) (equal? x y)]
                                                  [(? boolean? b) #:when (boolean? y) (equal? x y)]
                                                  [_ false]))
                                              (first args) (second args))]
    [_ (error "no primop with name " op "with airity " (length args))]))

; look up a given symbol in an enviroment
(define (lookup [val : Symbol] [env : Enviroment]) : Value
  (cond
    [(empty? env) (error "ZNQR: " val " not defined")]
    [(equal? val (Binding-name (first env))) (Binding-val (first env))]
    [else (lookup val (rest env))]))

;;> you're adding things to the end of the list and then reversing it every time you want
;;> to do a lookup; just add to the *front* of the list (constant-time instead of linear)
;;> and then look up starting at the front...

;extend the enviroment to contain a list bindings
(define  (extend-env [vals : (Listof Value)] [names : (Listof Symbol)] [env : Enviroment]) : Enviroment
  (cond
    [(and (empty? vals) (empty? names)) env]
    [(empty? names) (error "ZNQR: Parameter mismatch " vals names)]
    [(empty? vals) (error "ZNQR: Parameter mismatch " vals names)]
    [else (append (extend-env (rest vals) (rest names) env) (list (Binding (first names)
                                                                           (first vals))))]))
;evaluate an expression
(define (interp [value : ExprC] [env : Enviroment]) : Value
 (match value
   [(NumC v) v]
   [(StringC x) x]
   [(CondC v t e) (define val (interp v env))
                    (match val
                      [(? boolean? val) (cond
                                          [val (interp t env)]
                                          [else (interp e env)])]
                      [_ (error "ZNQR: condition not a boolean")])]
   [(IdC v) (lookup v (reverse env))]
   [(lamC a b) (ClosV  a b env)]
   [(AppC f a) (define fd (interp f env))
               (match fd
                 [(PrimopV sym) (do-primop sym (map (lambda ([x : ExprC]) (interp x env)) a))]
                 [(ClosV arg b enviro)(interp b
                                              (extend-env  (map (lambda ([x : ExprC]) (interp x env)) a)
                                                            arg enviro))]
                 [_ (error "ZNQR: Invalid function body")]
                 ;;> pull all of these trailing parens up...
                 )
                ]


    ))
;check to make sure parameter syntax is valid
(define (check-params [params : Sexp])
  (with-handlers
      ([exn? (lambda (e) (error "ZNQR: Bad Syntax in " params))])
    (cast params (Listof Symbol)))
  (match (check-duplicates (cast params (Listof Symbol)))
    [#f (cast params (Listof Symbol))]
    [_ (error "ZNQR: Duplicate argument in " params)]))

;parse an Sexp into a ExprC
(define (parse [input : Sexp]) : ExprC
  (match input
    [(? real? num) (NumC num)]
    [(? string? x) (StringC x)]
    [(list params arrow body) #:when (equal? '-> arrow) (lamC (check-params params)
                                                              (parse body))]
    [(list 'if exp then else) (CondC (parse exp) (parse then) (parse else))]
    [(? symbol? s)  #:when(not (hash-has-key? reserved s)) (IdC s)]
    [(list args ...) #:when (not (hash-has-key? reserved (first args)))
                     (AppC (parse (first args))
                           (map (lambda ([arg : Sexp]) (parse arg))
                                (cast (rest args) (Listof Sexp))))]
    [(list 'var args ... body) (parse-variables (cast args (Listof Sexp)) (parse body))]
    [_ (error "ZNQR: Unrecognized expression" input)]
    ))
;desugar variable syntax
(define (parse-variables [args : (Listof Sexp)] [body : ExprC]) : AppC
  (AppC
   (lamC  (check-params (map (lambda ([arg : Sexp]) : Symbol
                          (match arg
                            [(list sym '= exp) #:when (not (hash-has-key? reserved sym)) (cast sym Symbol)]
                            [_ (error "ZNQR: invalid symbol")]))
                             (cast args (Listof Sexp)))) body)
              (map (lambda ([arg : Sexp]) : ExprC
                          (match arg
                            [(list sym '= exp) (cast (parse exp) ExprC)])) (cast args (Listof Sexp)))))
;parse and evaluate a program
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-level-env)))

(check-equal? (serialize #f) "false")
(check-equal? (serialize #t) "true")
(check-equal? (serialize 4.2) "4.2")
(check-equal? (top-interp '{{} -> {+ 3 2}}) "#<procedure>")
(check-equal? (top-interp '"hi") "\"hi\"")

(check-equal? (top-interp '{{{} -> {+ 3 2}}}) "5")
(check-equal? (top-interp '{{{} -> {* 3 2}}}) "6")
(check-equal? (top-interp '{{{} -> {/ 3 3}}}) "1")
(check-equal? (top-interp '{{{} -> true}}) "true")
(check-equal? (top-interp '{{{a b} -> {<= a b}} 2 3}) "true")
(check-equal? (top-interp '{{{a b} -> {<= a b}} 4 3}) "false")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '{{{a b} -> {equal? a b}} 3 3}) "true")
(check-equal? (top-interp '{{{a b} -> {equal? a b}} 3 4}) "false")
(check-equal? (top-interp '{{{a b} -> {equal? a b}} 3 +}) "false")
(check-equal? (top-interp '{{{a b} -> {equal? a b}} true true}) "true")
(check-equal? (top-interp '{{{} -> {- 3 2}}}) "1")
(check-equal? (top-interp '{{{} -> {if true 1 2}}}) "1")
(check-equal? (top-interp '{{{} -> {if false 2 1}}}) "1")
(check-equal? (top-interp '{var {z = {+ 1 1}} {y = 1} {+ z y}}) "3")
(check-equal? (top-interp '{var {z = {+ 1 1}}
                                {y = {{{} -> {- 3 {+ {{{} -> {- 3 2}}}
                                                     {{{} -> {- 3 2}}}}}}}}
                                {+ z y}}) "3")
(check-equal? (top-interp '{var {z = {+ 1 1}}
                                {y = {{{} -> {- 3 {+ {{{} -> {- 3 2}}}
                                                     {{{} -> {- 3 2}}}}}}}}
                                {+ z y}}) "3")
(check-equal? (top-interp '{var {z = {+ 1 1}}
                                {y = {{{} -> {- 3 {var {x = 95} {y = 97} {- y x}}}}}}
                                {+ z y}}) "3")

(check-exn #px"no primop with name"
            (λ ()
              (top-interp '{{{} -> {+ 3 2 3}}})))
(check-exn #px"Bad Syntax"
            (λ ()
              (top-interp '{{{3 4 5} -> {+ 3 2}}})))
(check-exn #px"Duplicate"
            (λ ()
               (top-interp '{{{a a} -> {equal? a a}} true true})))
(check-exn #px"Unrecognized expression"
            (λ ()
              (top-interp '{{} -> {+ var if}})))
(check-exn #px"Parameter mismatch"
            (λ ()
              (top-interp '{{{} -> 9} 7})))
(check-exn #px"Parameter mismatch"
            (λ ()
              (top-interp '{{{x} -> 9}})))
(check-exn #px"not defined"
            (λ ()
              (top-interp 'q)))
(check-exn #px"invalid "
           (λ ()
(top-interp '(var (-> = "") "World"))))

(check-exn #px"invalid arguments"
            (λ ()
              (top-interp '{{{} -> {+ true 2}}})))
(check-exn #px"invalid arguments"
            (λ ()
              (top-interp '{{{} -> {- true 2}}})))
(check-exn #px"invalid arguments"
            (λ ()
              (top-interp '{{{} -> {* true 2}}})))
(check-exn #px"invalid arguments"
            (λ ()
              (top-interp '{{{} -> {/ true 2}}})))
(check-exn #px"invalid arguments"
            (λ ()
              (top-interp '{{{} -> {<= true 2}}})))
(check-exn #px"Divide by zero"
            (λ ()
              (top-interp '{{{} -> {/ 1 0}}})))
(check-exn #px"Invalid function body"
            (λ ()
              (top-interp '{{{} -> {true}}})))
(check-exn #px"condition not a boolean"
            (λ ()
               (top-interp '{{{} -> {if 1 1 1}}})))





