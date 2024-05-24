;;> (AUTOCOMMENT) Apparently missing a required structure: '("primV" "PrimV" "Pri...
#lang typed/racket

(require typed/rackunit)

; Full Project Implemented at 2:35 PM, 04/27/2022. Wednesday
; 180 lines of actual codes(incl. comments) + 200 lines of test cases
; Passed all Test Cases the first try! 10:45 PM Saturday


; some constant values we need.
(define RESERVED '(var in if =>))
(define PRIMITIVE '(+ / * - <= equal? error true false))
(define BI_OP '(+ / * - <= equal?))
(define ARITHM_OP '(+ / * -))
(define E "JILI") ; tired of typing JILI over and over for error test cases, so I use E here.
(define FUN "#<procedure>")
(define PRIM "#<primop>")

; ExprC section
(define-type ExprC (U NumC IdC AppC LamC StrC if))
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)]) #:transparent)
(struct LamC ([arg : (Listof Symbol)] [body : ExprC]) #:transparent)
;;> (AUTOCOMMENT) This structure represents an expression, end it with a "C".
(struct if ([test : ExprC] [t : ExprC] [f : ExprC]) #:transparent)

; Value section
(define-type Value (U NumV StrV CloV '+ '- '/ '* 'equal? 'error '<= 'true 'false))
(struct NumV ([n : Real]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct CloV ([arg : (Listof Symbol)] [body : ExprC] [env : Env]))

; Env section
(struct Binding ([name : Symbol] [val : Value]))
(define-type Env (Listof Binding))
(define extend-env append)
;;> this is shockingly space-efficient, but also quite unorthadox.
(define top-env (for/list : Env
                  ([i PRIMITIVE])
                  (Binding i (cast i Value))))

; BoolMap for easy converting to respective Value
(define bool-map (hash #t 'true
                       #f 'false))


; This top-interpreter combines all the helper functions and
; return the evaulated result of serialize function
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; Evaulate the value of the given ExprC with an env
; and return the result of it
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(IdC v) (lookup v env)]
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    [(LamC a b) (CloV a b env)]
    [(if test t f) (match (interp test env)
                     ['true (interp t env)]
                     ['false (interp f env)]
                     [_ (error 'interp "test expr has to be boolean ~e" E)])]
    [(AppC f a)
     (define f-val (interp f env))
     (check-arity f-val (length a)) ; check arity here
     (match f-val
       [(CloV args body clov-env) (interp body (extend-env
                                   (for/list : Env
                                     ([i args]
                                      [j a])
                                     (Binding i (interp j env)))
                                   clov-env))]
       [(app (λ (x) (member x BI_OP)) (? list?))
        (binop-lookup f-val (interp (first a) env) (interp (second a) env))]
       ['error (error "user-error" (serialize (interp (first a) env)))]
       [_ (error 'interp "~e is not a function ~e" f-val E)])]))


; return the serialization of Value "v" in String
(define (serialize [v : Value]) : String
  (match v
    [(NumV n) (~v n)]
    [(StrV s) (~v s)]
    ['true "true"]
    ['false "false"]
    [(CloV arg body env) FUN]
    [(? symbol? s) PRIM]))


; look up a variable inside env to find what vaule it is
(define (lookup [v : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "I don't know this variable ~e ~e" v E)]
    [(symbol=? v (Binding-name (first env))) (Binding-val (first env))]
    [else (lookup v (rest env))]))


; check that arity is okay. Error out if not. Nothing happens if yes.
(define (check-arity fun [len : Natural])
  (define actual (match fun
                   [(? symbol? s)
                    #:when (member s BI_OP)
                    2]
                   [(CloV args _ _) (length args)]
                   ['error 1]
                   ['if 3]
                   [_ len]))
  (unless (= actual len)
    (error 'check-arity "Wrong arity for ~e ~e" fun E)))


; calculate result for binop operators
(define (binop-lookup [op : Symbol] [l : Value] [r : Value]) : Value
  (cond
    [(symbol=? 'equal? op) ; equal? comes first because l r can be any Value for equal?
     (match* (l r)
       [('true 'true) 'true]
       [((StrV a) (StrV b)) (hash-ref bool-map (equal? a b))]
       [((NumV a) (NumV b)) (hash-ref bool-map (= a b))]
       [(_ _) 'false])]

    [(and (NumV? l) (NumV? r)) ; the remaining binop needs both NumV
     (match op
       ['<= (hash-ref bool-map (<= (NumV-n l) (NumV-n r)))]
       [(app (λ (x) (member x ARITHM_OP)) (? list?))
        (NumV (arithm-lookup op (NumV-n l) (NumV-n r)))])]

    [else (error 'binop-lookup "one argument for ~e is not a number ~e" op E)]))


; Determine the operator type for given arithm data and return its evaulated result.
(define (arithm-lookup [s : Symbol] [l : Real] [r : Real]) : Real
  (match s
    ['* (* l r)]
    ['- (- l r)]
    ['+ (+ l r)]
    ['/ (when (zero? r) ; special case for / to check division by 0 exception
            (raise-argument-error 'arithm-lookup/divide
                   "nonzero number" E))
            (/ l r)]))


; Parse the given S-expression and return its ExprC form.
(define (parse [s : Sexp]) : ExprC
  (match s
    [(list (? symbol? s) ... '=> v) ; LamC
     (define args (cast s (Listof Symbol)))
     (unless (andmap is-not-reserved? args) (error 'parse "~e contains reserved keyword! ~e" args E))
     (when (check-duplicates args) (error 'parse "~e arg duplicates. ~e" args E))
     (LamC args (parse v))]

    [(list 'if a ...) ; if
     (check-arity 'if (length a))
     (if (parse (first a)) (parse (second a)) (parse (third a)))]

    [(list 'var (list (? list? l) ...) 'in e) ; var
     (define ll (cast l (Listof (Listof Sexp))))
     (define fun (append
       (for/list ([i ll]) : (Listof Sexp)
       (match i
         [(list (? symbol? s) '= v) s]
         [_ (error 'parse "var syntax error for ~e ~e" i E)]))
       (list '=> e)))
     (define vals ((inst map Sexp (Listof Sexp)) third ll))
     (AppC (parse fun) (map parse vals))]

    [(list fun values ...) ; AppC
     (AppC (parse fun) (map parse values))]

    [(? symbol? s) ; IdC
     #:when (is-not-reserved? s)
     (IdC s)]
    [(? string? str) (StrC str)] ; StrC
    [(? real? n) (NumC n)] ; NumC
    [_ (error 'parse
                  "S-expression ~e not supported or reserved keyword used ~e"
                  s E)]))


; Return true if a given symbol is not reserved
(define (is-not-reserved? [s : Symbol]) : Boolean
  (not (member s RESERVED)))


; ================================ TEST CASES START HERE ===========================================
(check-equal? (top-interp '{a => 1}) FUN)
(check-equal? (top-interp '{a => {v => {a v}}}) FUN)
(check-equal? (top-interp '{f => {f 8}}) FUN)
(check-equal? (top-interp '{{a => 1} 5}) "1")
(check-equal? (top-interp '{{a => "hi"} 5}) (~v "hi"))
(check-equal? (top-interp '{{a => false} 5}) "false")
(check-equal? (top-interp '{{a => {equal? 1 1}} 5}) "true")
(check-equal? (top-interp '{{a => {<= 1 0}} 5}) "false")
(check-equal? (top-interp '{{a => {* 2 5}} 0}) "10")
(check-equal? (top-interp '{{f => {f 8}} {v => {* 2 v}}}) "16")
(check-equal? (top-interp '{{{a => {v => {a v}}} {v => {* 2 v}}} 10}) "20")
(check-equal? (top-interp '{{{a => {v vv => {+ {a v} {a vv}}}} {v => {* 2 v}}} 10 100}) "220")

(check-equal? (top-interp
               '{{add one two => {{three => {{double => {{val => {{three double} val}}
                                           10}}
                               {val => {* 2 val}}}}
                   {{add one} two}}}
   {f => {g => {fun => {val => {{f fun} {{g fun} val}}}}}}
   {f => {val => {f val}}}
   {f => {val => {f {f val}}}}})
              "80")

(check-equal? (top-interp
   '{{{{{one => {two => {fun => {val => {{one fun} {{two fun} val}}}}}}
    {fun => {val => {fun val}}}}
   {fun => {val => {fun {fun val}}}}}
  {val => {* 2 val}}}
 10})
              "80")

(check-equal? (top-interp '{ => (error {+ 3 5})}) FUN)
(check-equal? (top-interp '{{ => {+ 1 1}}}) "2")
(check-equal? (top-interp '{{ => {/ 6 2}}}) "3")
(check-equal? (top-interp '{{ => {if true 1 2}}}) "1")
(check-equal? (top-interp '{{ => {if {<= 2 3} {+ 1 1} 5}}}) "2")
(check-equal? (top-interp '{if false 1 9}) "9")

(check-equal?
 (top-interp '{var {[z = {+ 9 14}]
      [y = 98]}
     in
     {+ z y}})
 "121")

(check-equal?
 (top-interp '{var {[add = {f => {g => {fun => {val => {{f fun} {{g fun} val}}}}}}]
        [one = {f => {val => {f val}}}]
        [two = {f => {val => {f {f val}}}}]}
       in
       {var {[three = {{add one} two}]
             [fun = {val => {* 2 val}}]
             [val = 10]}
            in
            {{three fun} val}}})
 "80")

(check-equal?
 (top-interp '{var {}
                  in
                  5})
 "5")

(check-equal?
 (top-interp '{var {[x = 1]
                    [y = 5]}
                   in
                   {- x y}})
 "-4")

(check-equal?
 (top-interp '{{{x => {y => {- x y}}} 1} 5})
 "-4")

(check-equal? (serialize '+) PRIM)
(check-equal? (serialize '-) PRIM)
(check-equal? (serialize '+) PRIM)
(check-equal? (serialize '*) PRIM)
(check-equal? (serialize 'true) "true")

(check-equal? (top-interp '{equal? + -}) "false")
(check-equal? (top-interp '{equal? 1 1}) "true")
(check-equal? (top-interp '{equal? "hi" "hi"}) "true")
(check-equal? (top-interp '{equal? true true}) "true")
(check-equal? (top-interp '{equal? false true}) "false")
(check-equal? (top-interp '{equal? "+" +}) "false")
(check-equal? (top-interp '{equal? {x => 1} {x => 1}}) "false")
(check-equal? (top-interp '{equal? {<= 4 5} true}) "true")
(check-equal? (top-interp '{equal? + +}) "false")

(check-equal? (top-interp '{if {<= 4 5} {* 1 3} 10}) "3")
(check-equal? (top-interp '{if {equal? 1 2} 3 {x => 1}}) FUN)

(check-equal? (top-interp 1) "1")

; ========================================== ERROR test cases START HERE ============================================
(check-exn ; reserved keyword
 (regexp (regexp-quote E))
 (λ () (top-interp '{in => 1})))

(check-exn ; duplicate arg names
 (regexp (regexp-quote E))
 (λ () (top-interp '{a a => 1})))

(check-exn ; user-error
 (regexp (regexp-quote "500003"))
;;> (AUTOCOMMENT) Grader: most of these are errors, but be sure to check whether this message is warranted:
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
 (λ () (top-interp '{{ => (error {+ 3 500000})}})))

(check-exn ; too many arg
 (regexp (regexp-quote E))
 (λ () (top-interp '{{a => {+ 1 1 1}} 0})))

(check-exn ; arithm on non-number
 (regexp (regexp-quote E))
 (λ () (top-interp '{{a => {+ "hi" a}} 0})))

(check-exn ; a is not a function
 (regexp (regexp-quote E))
 (λ () (top-interp '{{a => {a b}} 0})))

(check-exn ; can't find b
 (regexp (regexp-quote E))
 (λ () (top-interp '{{a => {b a}} 0})))

(check-exn ; boolean is not a function
 (regexp (regexp-quote E))
 (λ () (top-interp '{{a => {false a}} 0})))

(check-exn ; error must have only 1 arg
 (regexp (regexp-quote E))
;;> (AUTOCOMMENT) Grader: most of these are errors, but be sure to check whether this message is warranted:
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
 (λ () (top-interp '{{ => (error)}})))

(check-exn ; divide by 0
 (regexp (regexp-quote E))
 (λ () (top-interp '{{a => {/ a {+ 0 0}}} 1})))

(check-exn ; wrong arity
 (regexp (regexp-quote E))
 (λ () (top-interp '{{ => 5} 0 0 0})))

(check-exn ; wrong syntax
 (regexp (regexp-quote E))
 (λ () (top-interp '{a => => })))

(check-exn ; if having too few args
 (regexp (regexp-quote E))
 (λ () (top-interp '{{ => {if {equal? 5 5} 5}}})))

(check-exn ; if having too many args
 (regexp (regexp-quote E))
 (λ () (top-interp '{{ => {if {equal? 5 5} 5 10 10}}})))

(check-exn ; if test expr is not a boolean
 (regexp (regexp-quote E))
 (λ () (top-interp '{if 1 1 1})))

(check-exn ; bad var syntax
 (regexp (regexp-quote E))
 (λ () (top-interp '{var {[a > 5]}
                         in
                         {+ a 1}})))

(check-exn ; bad var syntax
 (regexp (regexp-quote E))
 (λ () (top-interp '{var {[a = 5]}
                         {+ a 1}})))

(check-exn ; bad var syntax
 (regexp (regexp-quote E))
 (λ () (top-interp '{var {[a = 5]}
                         in
                         {+ b 1}})))

(check-exn ; bad var syntax
 (regexp (regexp-quote E))
 (λ () (top-interp '{var {[]}
                  in
                  5})))

(check-exn ; not a function
 (regexp (regexp-quote E))
 (λ () (top-interp '{{+ 1 2} 3})))
