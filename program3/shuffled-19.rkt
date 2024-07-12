#lang typed/racket

;;> eyeball: 4/6, Some errors, see below

(require typed/rackunit)

; This project is failing 2 tests
; I've implemeted all features, but edge cases are missed.

; Value definition
(define-type Value (U numV boolV closV primV))
(struct numV ([val : Real]) #:transparent)
(struct boolV ([val : Boolean]) #:transparent)
(struct closV ([arg : (Listof Symbol)] (body : ExprC) (env : Env)) #:transparent)
(struct primV ([op : Symbol]) #:transparent)

; Type definition for ExprC
(define-type ExprC (U numC idC appC lamC ifC))
(struct numC ([n : Real]) #:transparent)
(struct stringC ([str : String]) #:transparent) 
(struct idC ([s : Symbol]) #:transparent)
(struct varC ([ids : ExprC]) #:transparent)
(struct appC ([fun : ExprC][arg : (Listof ExprC)]) #:transparent)
(struct ifC ([test : ExprC][then : ExprC][else : ExprC]))
(struct lamC ([arg : (Listof Symbol)][body : ExprC]) #:transparent)

; Binding definition
(define-type Binding bind)
(struct bind ([name : Symbol][val : Value]) #:transparent)

; Environment definitions
(define-type Env (Listof Binding))

; Hash table for restricted symbols
(define restricted (make-immutable-hash (list (cons 'var 0)
                                              (cons 'if 0)
                                              (cons '-> 0)
                                              (cons '= 0))))

; Top Environment that contains primitives
(define top-env (list (bind '+ (primV '+))
                      (bind '- (primV '-))
                      (bind '* (primV '*))
                      (bind '/ (primV '/))
                      (bind '<= (primV '<=))
                      (bind 'equal? (primV 'equal?))
                      (bind 'true (boolV true))
                      (bind 'false (boolV false))
                      (bind 'if (primV 'ifC))))

; Given an Sexp, parse the Sexp, and then interp it. Returns a Real.
(: top-interp (-> Sexp String))
(define (top-interp s)
  (serialize (interp (parse s) top-env)))

; Parser for Sexp and returns ExprC
; Takes in the body of the Sexp from parse-fundef
(: parse (-> Sexp ExprC))
(define (parse s)
  (match s
    [(list 'var stuff ...) (parse-helper (desugar s))]
    [else (parse-helper s)]))

; Intermediate function that handles non-var parsing
(: parse-helper (-> Sexp ExprC))
(define (parse-helper s)
  (cond
    [(real? s) (numC s)]
    [(symbol? s)
     (if (not (hash-has-key? restricted s))
         (idC s)
         (error 'ZNQR "Cannot use a restricted symbol"))]
    [(list? s) (parse-list s)]
    [else (error 'ZNQR "Invalid input")]))

; Helper function to parse a list
(: parse-list (-> (Listof Sexp) ExprC))
(define (parse-list s)
  (match s
    ; lamC match
    [(list args '-> body) (lamC (check-args (sexpToList args)) (parse body))]
    ; appC match
    ;;> these can be combined into one 
    [(list (? symbol? op) args ...) (appC (idC op) (map (lambda (a) (parse a)) args))]
    ; appC match for initial pass
    [(list main args ...) (appC (parse main) (map (lambda (arg) (parse arg)) args))]))

(: check-args (-> (Listof Symbol) (Listof Symbol)))
(define (check-args l)
  (if (not (check-duplicates l))
      l
      (error 'ZNQR "Duplicate parameters found")))

; Given a var Sexp, desugar it into an Sexp that can be interped
(: desugar (-> Sexp Sexp))
(define (desugar s)
  (match s
    [(list 'var (? list? stuff) ... body)
     (local ([define params (map (lambda ([x : Sexp]) (getParams x)) (cast stuff (Listof Sexp)))]
             [define args (map (lambda ([x : Sexp]) (getArgs x)) (cast stuff (Listof Sexp)))])
       (cons (list params '-> body) args))]))

; Helper function to get the parameters of an Sexp
(: getParams (-> Sexp Sexp))
(define (getParams s)
  (match s
    [(list p '= args) p]))

; Helper function to get the arguments of an Sexp
(: getArgs (-> Sexp Sexp))
(define (getArgs s)
  (match s
    [(list p '= args) args]))

; An interpreter for ExprC
(: interp (-> ExprC Env Value))
(define (interp exp env)
  (match exp
    [(numC x) (numV x)]
    [(appC fun args)
     (match (interp fun env)
       ;;> ifC is not a primop
       [(primV op) (if (equal? op 'ifC)
                       (local ([define test (interp (first args) env)])
                         (if (boolV? test)
                             (if (boolV-val test)
                                 (interp (second args) env)
                                 (interp (third args) env))
                             (error 'ZNQR "Test does not return a boolean")))
                       (prim-handler op
                                     ;;> no check for arity here
                                     (interp (first args) env)
                                     (interp (second args) env)))]
       [(closV param body clo-env)
        (if (equal? (length param) (length args))
            (local ([define new-env (append (map (lambda ([name : Symbol][exp : ExprC])
                                                   (bind name (interp exp env)))
                                                 param
                                                 args)
                                            clo-env)])
              (interp body new-env))
            (error 'ZNQR "Params and args do not match length"))]
       ;;> what is this case for? if should be its own case
       [(boolV val) (match args
                      [(list a b)
                       (if val
                           (interp a env)
                           (interp b env))])]
       [else (error 'ZNQR "Operator must be a primV")])]
    ;;> this is the only if you should have
    [(ifC test then else) (local ([define val (interp test env)])
                            (match val
                              [(boolV x) (if x
                                             (interp then env)
                                             (interp else env))]
                              [else (error 'ZNQR "Op is not a boolean")]))]
    [(idC x) (lookup x env)]
    [(lamC arg body) (closV arg body env)]))

; Primitive operations handler
(: prim-handler (-> Symbol Value Value Value))
(define (prim-handler op l r)
  (if (or (primV? l) (primV? r))
      (error 'ZNQR "Left or right value cannot be a primV")
      (if (and (numV? l) (numV? r))
          (match op
            [(? symbol? '+) (numV (+ (numV-val l) (numV-val r)))]
            [(? symbol? '-) (numV (- (numV-val l) (numV-val r)))]
            [(? symbol? '*) (numV (* (numV-val l) (numV-val r)))]
            [(? symbol? '/) (if (equal? 0 (numV-val r))
                                (error 'ZNQR "Division by zero")
                                (numV (/ (numV-val l) (numV-val r))))]
            [(? symbol? '<=) (if (<= (numV-val l) (numV-val r))
                                 (boolV #t)
                                 (boolV #f))]
            [(? symbol? 'equal?) (if (equal? l r)
                                     (boolV #t)
                                     (boolV #f))])
          (match op
            [(? symbol? 'true) (boolV #t)]
            [(? symbol? 'false) (boolV #f)]))))

; Given a symbol, look through the bindings in the env and return the
; respective value if it exists, otherwise, error.
; lookup should return either a closV or a primV
(: lookup (-> Symbol Env Value))
(define (lookup for env)
  (cond
    [(empty? env) (error 'ZNQR "Binding not found")]
    [else (if (symbol=? for (bind-name (first env)))
                  (bind-val (first env))
                  (lookup for (rest env)))]))

; Helper function to turn a Sexp to a list of symbols
(: sexpToList (-> Sexp (Listof Symbol)))
(define (sexpToList s)
  (match s
    [(list a b ...) (if (symbol? a)
                        (cons a (sexpToList b))
                        (error 'ZNQR "Invalid argument"))]
    [else '()]))

; Given a value, return the string representation
(: serialize (-> Value String))
(define (serialize val)
  (match val
    [(numV x) (~v x)]
    [(boolV x) (if x
                   "true"
                   "false")]
    [(closV args body env) "#<procedure>"]
    [(primV op) "#<primop>"]))

; ===========================
;         TEST CASES
; ===========================
(define f1 '{{{x y} -> {* 6 7}}
             {{x} -> 2}
             {{y} -> 5}})
(define f2 '{{{f g} -> {+ {f 2} {g 9}}}
             {{x} -> {+ x 1}}
             {{x} -> {+ x 2}}})
(define f3 '{{{} -> {ifC (<= 1 2) 1 2}}})
(define f4 '{{{minus} -> {{{a b} -> {minus a b}} 4 3}}
             {{x y} -> {- x y}}})
(define f5 '{{} -> {+ 1 2}})
(define f6 '{{{f g} -> {/ {f 2} {g 9}}}
             {{x} -> 5}
             {{x} -> 0}})
(define f6.1 '{{{f g} -> {/ {f 2} {g 9}}}
               {{x} -> 24}
               {{x} -> 3}})
(define f7 '{{{x y} -> {{<= 3 2} 5 4}}
             {{x} -> 2}
             {{y} -> 5}})
(define f7.1 '{{{x y} -> {{<= 2 3} 5 4}}
               {{x} -> 2}
               {{y} -> 5}})
(define f8 '{{{x y} -> {{equal? 3 2} 5 4}}
             {{x} -> 2}
             {{y} -> 5}})
(define f8.1 '{{{x y} -> {{equal? 3 3} 5 4}}
               {{x} -> 2}
               {{y} -> 5}})
(define f8.2 '{{{x y} -> {{equal? 3 2} fun 4}}
               {{x} -> 2}
               {{y} -> 5}})
(define f8.3 '{{{x y} -> {{equal? 3 3} cool 4}}
               {{x} -> 2}
               {{y} -> 5}})
(define f8.4 '{{{x y} -> {{equal? 3 3} - 4}}
               {{x} -> 2}
               {{y} -> 5}})
(define f9 '{{{x y} -> {{ifC 3 2} 5 4}}
             {{x} -> 2}
             {{y} -> 5}})

; top-interp tests
(check-equal? (top-interp f1) "42")
(check-equal? (top-interp f2) "14")
(check-equal? (top-interp f4) "1")
(check-equal? (top-interp f5) "#<procedure>")
(check-exn (regexp (regexp-quote "Division by zero"))
           (lambda () (top-interp f6)))
(check-equal? (top-interp f6.1) "8")
(check-equal? (top-interp f7) "4")
(check-equal? (top-interp f7.1) "5")
(check-equal? (top-interp f8) "4")
(check-equal? (top-interp f8.1) "5")
(check-equal? (top-interp f8.2) "4")
(check-exn (regexp (regexp-quote "Binding not found"))
           (lambda () (top-interp f8.3)))
(check-exn (regexp (regexp-quote "Invalid input"))
           (lambda () (parse "Cool")))
(check-exn (regexp (regexp-quote "Params and args do not match length"))
           (lambda () (top-interp '((() -> 9) 17))))
(check-equal? (top-interp '{if {<= 4 3} 434 true}) "true")
(check-equal? (top-interp '{if {<= 3 4} 434 true}) "434")
(check-exn (regexp (regexp-quote "Test does not return a boolean"))
           (lambda () (top-interp '{if {+ 4 3} 434 true})))
(check-exn (regexp (regexp-quote "Left or right value cannot be a primV"))
           (lambda () (top-interp '(+ + +))))
(check-exn (regexp (regexp-quote "Operator must be a primV"))
           (lambda () (top-interp `(3 4 5))))

; interp tests
(check-equal? (interp (ifC (idC 'a) (idC 'b) (idC 'c)) (list (bind 'a (boolV true))
                                                             (bind 'b (numV 1))
                                                             (bind 'c (numV 0))))
              (numV 1))
(check-equal? (interp (ifC (idC 'a) (idC 'b) (idC 'c)) (list (bind 'a (boolV false))
                                                             (bind 'b (numV 1))
                                                             (bind 'c (numV 0))))
              (numV 0))
(check-exn (regexp (regexp-quote "Op is not a boolean"))
           (lambda () (interp (ifC (idC 'a) (idC 'b) (idC 'c)) (list (bind 'a (numV 10))
                                                                     (bind 'b (numV 1))
                                                                     (bind 'c (numV 0))))))

; prim-handler tests
(check-equal? (prim-handler 'true (boolV true) (boolV false)) (boolV true))
(check-equal? (prim-handler 'false (boolV true) (boolV false)) (boolV false))

; serialize tests
(check-equal? (serialize (numV 10)) "10")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (primV '+)) "#<primop>")

; var tests
(check-equal? (desugar '{var {z = {+ 9 14}}
                             {y = 98}
                             {+ z y}})
              '{{{z y} -> {+ z y}}
                {+ 9 14}
                98})

; parse test
(check-equal? (parse '{var {z = {+ 9 14}}
                           {y = 98}
                           {+ z y}})
              (appC (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
                    (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
(check-exn (regexp (regexp-quote "Duplicate parameters found"))
           (lambda () (parse '((x x) -> 3))))
(check-exn (regexp (regexp-quote "Invalid argument"))
           (lambda () (parse '((3 4 5) -> 6))))

; parse-helper test
(check-exn (regexp (regexp-quote "Cannot use a restricted symbol"))
           (lambda () (parse '=)))
