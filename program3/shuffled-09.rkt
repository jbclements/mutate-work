#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)


; DATA STRUCTURES

(define-type ExprC
  (U NumC IdC StringC If LamC AppC))

(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct If ([cond : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct LamC ([arg : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)

(define-type Value
  (U NumV BoolV StringV ClosV PrimOpV))

(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV ([s : Symbol]) #:transparent)

(define-type Binding Bind)
(struct Bind ([name : Symbol] [val : Value]))
(define-type-alias Env (Listof Binding))

; returns defaults for top level environment
(define (get-top-level-env) : Env
  (list (Bind 'true (BoolV #t))
        (Bind 'false (BoolV #f))
        (Bind '+ (PrimOpV '+))
        (Bind '- (PrimOpV '-))
        (Bind '* (PrimOpV '*))
        (Bind '/ (PrimOpV '/))
        (Bind '<= (PrimOpV '<=))
        (Bind 'equal? (PrimOpV 'equal?))
        ))

(define top-env (get-top-level-env))
(define extend-env cons)



; == FUNCTIONS ==


; EVALUATOR


; parses and evaluates the ZQNR language
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))


; evaluates the abtract syntax tree for the ZNQR language
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
      [(NumC n) (NumV n)]
      [(StringC s) (StringV s)]
      [(IdC s) (lookup s env)]
      [(If cond then else) (eval-If cond then else env)]
      [(AppC f args)
        (match (interp f env)
          [(PrimOpV op) (eval-PrimOpV op (map (lambda ([x : ExprC]) (interp x env)) args))]
          [(ClosV clos-args body clos-env)
           (interp body (bind-each clos-env clos-args args env))]
          [else (error 'ZNQR "input not formatted")])]
      [(LamC args body) (ClosV args body env)]))


; handles If case
(define (eval-If [cond : ExprC] [then : ExprC] [else : ExprC] [env : Env]) : Value
  (define cond-result (interp cond env))
  (if (BoolV? cond-result)
      (if (BoolV-b cond-result)
          (interp then env)
          (interp else env))
      (error 'ZNQR "if test statement is not boolean ~e" cond)))


; handles the PrimOpV case
(define (eval-PrimOpV [s : Symbol] [args : (Listof Value)]) : Value
  (match s
    ['+ (eval-plus args)]
    ['- (eval-sub args)]
    ['* (eval-mult args)]
    ['/ (eval-div args)]
    ['<= (eval-leq args)]
    ['equal? (eval-equal? args)]))


; evals + case
(define (eval-plus [args : (Listof Value)]) : Value
  (if (and (= (length args) 2) (NumV? (first args)) (NumV? (last args)))
            (NumV (+ (NumV-n (cast (first args) NumV)) (NumV-n (cast (last args) NumV))))
            (error 'ZNQR "cannot add ~e" args)))


; evals - case
(define (eval-sub [args : (Listof Value)]) : Value
  (if (and (= (length args) 2) (NumV? (first args)) (NumV? (last args)))
            (NumV (- (NumV-n (cast (first args) NumV)) (NumV-n (cast (last args) NumV))))
            (error 'ZNQR "cannot subtract ~e" args)))


; evals * case
(define (eval-mult [args : (Listof Value)]) : Value
  (if (and (= (length args) 2) (NumV? (first args)) (NumV? (last args)))
            (NumV (* (NumV-n (cast (first args) NumV)) (NumV-n (cast (last args) NumV))))
            (error 'ZNQR "cannot multiply ~e" args)))


; evals / case
(define (eval-div [args : (Listof Value)]) : Value
  (if (and (= (length args) 2) (NumV? (first args)) (NumV? (last args)) (not (= 0 (NumV-n (cast (last args) NumV)))))
            (NumV (/ (NumV-n (cast (first args) NumV)) (NumV-n (cast (last args) NumV))))
            (error 'ZNQR "cannot divide ~e" args)))


; evals <= case
(define (eval-leq [args : (Listof Value)]) : Value
  (if (and (= (length args) 2) (NumV? (first args)) (NumV? (last args)))
            (BoolV (or (= (NumV-n (cast (first args) NumV)) (NumV-n (cast (last args) NumV)))
                       (< (NumV-n (cast (first args) NumV)) (NumV-n (cast (last args) NumV)))))
            (error 'ZNQR "cannot compare ~e" args)))


; evals equal? case
(define (eval-equal? [args : (Listof Value)]) : Value
  (if (and (= (length args) 2)
           (not (or (ClosV? (first args)) (PrimOpV? (first args))))
           (not (or (ClosV? (last args)) (PrimOpV? (last args)))))
            (BoolV (equal? (first args) (last args)))
            (BoolV #f)))


; binds each argument to a value
(define (bind-each [clos-env : Env] [names : (Listof Symbol)] [args : (Listof ExprC)] [env : Env]) : Env
  (if (= (length names) (length args))
      (match args
        [(and (? empty? args) (? empty? names)) clos-env]
        [else (extend-env (Bind (first names) (interp (first args) env))
                         (bind-each clos-env (rest names) (rest args) env))])
      (error 'ZNQR "incorret number of args")))


; looks up the value of a symbol in an environment
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'ZNQR "name not found for: ~e" for)]
    [else (cond
            [(symbol=? for (Bind-name (first env)))
             (Bind-val (first env))]
            [else (lookup for (rest env))])]))



; PARSING


; transforms an Sexp to an ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    [(? symbol? s) (parse-symbol s)]
    [(? string? s) (StringC s)]
    [(list 'if exprs ...) (parse-if exprs)]
    [(list 'var exprs ...) (desugar-var exprs '() '())]
    [(list (list (? symbol? args) ...) '-> body) (parse-LamC (cast args (Listof Symbol)) body)]
    [(list name expr ...) (AppC (parse name) (map parse expr))]
    [else (error 'ZNQR "input not well-formed: ~e" s)]))


; desugars var case
(define (desugar-var [exprs : (Listof Sexp)] [names : (Listof Symbol)] [values : (Listof ExprC)]) : ExprC
  (if (has-duplicates? names)
      (error 'ZNQR "duplicate argument name ~e" names)
      (if (= (length exprs) 1)
          (AppC (LamC names (parse (first exprs))) values)
          (match (first exprs)
            [(list (? symbol? name) '= val) (desugar-var (rest exprs)
                                                         (add-name name names)
                                                         (append values (list (parse val))))]))))


; safely add correct symbol
(define (add-name [name : Symbol] [names : (Listof Symbol)]) : (Listof Symbol)
  (if (valid-single-symbol? name)
      (append names (list name))
      (error 'ZNQR "incorrect usage of ~e" name)))


; parses 'if case
(define (parse-if [exprs : (Listof Sexp)]) : ExprC
  (if (= (length exprs) 3)
      (match exprs [(list cond then else) (If (parse cond) (parse then) (parse else))])
      (error 'ZNQR "if malformed: ~e" exprs)))


; parses the LamC case
(define (parse-LamC [args-list : (Listof Symbol)] [body : Sexp]) : ExprC
  (if (has-duplicates? args-list)
      (error 'ZNQR "repeated parameter name in ~e" args-list)
      (if (args-valid-names args-list)
          (LamC args-list (parse body))
          (error 'ZNQR "invalid arg names ~e" args-list))))


; check whether all args are valid names
(define (args-valid-names [args : (Listof Symbol)]) : Boolean
  (match args
    [(? empty? args) #t]
    ; [else (and (valid-variable-name? (first args))
    [else (and (valid-single-symbol? (first args))
               (args-valid-names (rest args)))]))


; parse a single symbol
(define (parse-symbol [s : Symbol]) : ExprC
  (if (valid-single-symbol? s)
      (IdC s)
      (error 'ZNQR "incorrect usage of ~e" s)))


; checks if single symbol is valid
(define (valid-single-symbol? [s : Symbol]) : Boolean
  (and (not (eq? 'var s))
       (not (eq? 'if s))
       (not (eq? '-> s))
       (not (eq? '= s))))


; returns true if duplicates are found in the list
(define (has-duplicates? [lst : (Listof Symbol)]) : Boolean
  (cond
     [(empty? lst) #f]
     [(not (not (member (first lst) (rest lst)))) #t]
     [else (has-duplicates? (rest lst)) ]))


; transforms a Value into a printable string
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (number->string n)]
    [(BoolV b) (if b
                   "true"
                   "false")]
    [(StringV s) s]
    [(ClosV args body env) "#<procedure>"]
    [(PrimOpV args) "#<primop>"]))



; == TEST CASES ==

(check-equal? (parse '{var 3})
              (AppC (LamC '() (NumC 3)) '()))
(check-equal? (parse (quote {if {{{a b} -> true} 5 6}
                                6
                                7}))
              (If (AppC (LamC '(a b) (IdC 'true)) (list (NumC 5) (NumC 6)))
               (NumC 6)
               (NumC 7)))
(check-exn (regexp (regexp-quote "ZNQR: incorrect usage of '="))
           (lambda () (parse '(var (= = (() -> 3)) (a = 9) (/)))))
(check-exn (regexp (regexp-quote "ZNQR: invalid arg names '(=)"))
           (lambda () (parse-LamC (list '=) (list 'a))))
(check-exn (regexp (regexp-quote "ZNQR: input not formatted"))
           (lambda () (top-interp '{{{{} -> 3}} 4 5} )))
(check-exn (regexp (regexp-quote "ZNQR: incorret number of args"))
           (lambda () (top-interp '{{{} -> 3} 4 5})))
(check-exn (regexp (regexp-quote "ZNQR: duplicate argument name '(z z)"))
           (lambda () (parse '(var (z = (() -> 3)) (z = 9) (z)))))
(check-exn (regexp (regexp-quote "ZNQR: incorret number of args"))
           (lambda () (top-interp '{{{x y} -> {+ x 2}} 3})))
(check-equal? (top-interp '{if {<= 0 0} 13 {/ 1 0}})
              "13")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {+ z y}})
              "121")
(check-equal? (top-interp '{{{z y} -> {+ z y}}
                             {+ 9 14}
                             98})
              "121")
(check-equal? (top-interp '{{z y} -> {+ z y}})
              "#<procedure>")
(check-equal? (top-interp '{{{z y} -> {+ z y}}
                             {{{x} -> {* x 2}} 4}
                             8})
              "16")
(check-equal? (top-interp '{{{z y x a} -> {+ z {+ y {* x a}}}}
                             5
                             5
                             5
                             0})
              "10")
(check-equal? (top-interp '{{{x} -> {- x {+ 5 2}}}
                             10})
              "3")
(check-equal? (top-interp '{{{x} -> {- x {{{z} -> {* z 2}} 5}}}
                             10})
              "0")
(check-exn (regexp (regexp-quote "ZNQR: input not well-formed: #t"))
           (lambda () (parse #t) ))
(check-exn (regexp (regexp-quote "ZNQR: name not found for: 'x"))
           (lambda () (interp (If (IdC 'true) (IdC 'x) (NumC 6)) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: incorrect usage of '->"))
           (lambda () (parse-symbol '->)))
(check-exn (regexp (regexp-quote "ZNQR: incorret number of args"))
           (lambda () (interp (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'y) (IdC 'x))))
                                                  (list (NumC 5) (NumC 5) (NumC 6))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: incorret number of args"))
           (lambda () (interp (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'y) (IdC 'x))))
                                                  (list (NumC 5))) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: cannot add (list (NumV 5) (NumV 5) (NumV 5))"))
           (lambda () (eval-plus (list (NumV 5) (NumV 5) (NumV 5)))))
(check-exn (regexp (regexp-quote "ZNQR: cannot subtract (list (NumV 5) (NumV 5) (NumV 5))"))
           (lambda () (eval-sub (list (NumV 5) (NumV 5) (NumV 5)))))
(check-exn (regexp (regexp-quote "ZNQR: cannot divide (list (NumV 5) (NumV 5) (NumV 5))"))
           (lambda () (eval-div (list (NumV 5) (NumV 5) (NumV 5)))))
(check-exn (regexp (regexp-quote "ZNQR: cannot multiply (list (NumV 5) (NumV 5) (NumV 5))"))
           (lambda () (eval-mult (list (NumV 5) (NumV 5) (NumV 5)))))
(check-exn (regexp (regexp-quote "ZNQR: cannot compare (list (NumV 5) (NumV 5) (NumV 5))"))
           (lambda () (eval-leq (list (NumV 5) (NumV 5) (NumV 5)))))
(check-equal? (eval-equal? (list (NumV 5) (NumV 5) (NumV 5)))
              (BoolV #f)
              )
(check-equal? (parse '{var {z = {+ 9 14}}
                           {y = 98}
                           {+ z y}})
              (AppC (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                          (NumC 98) )))
(check-equal? (interp (If (IdC 'true) (NumC 5) (NumC 6)) top-env)
              (NumV 5)
              )
(check-equal? (interp (If (IdC 'false) (NumC 5) (NumC 6)) top-env)
              (NumV 6)
              )
(check-exn (regexp (regexp-quote "ZNQR: if test statement is not boolean (NumC 1)"))
           (lambda () (interp (If (NumC 1) (NumC 5) (NumC 6)) top-env)))
(check-equal? (parse '{if x 5 6})
              (If (IdC 'x) (NumC 5) (NumC 6)))
(check-exn (regexp (regexp-quote "ZNQR: if malformed: '(true 5)"))
           (lambda () (parse '{if true 5})))
(check-equal? (parse '{if true 5 6})
              (If (IdC 'true) (NumC 5) (NumC 6)))
(check-exn (regexp (regexp-quote "ZNQR: repeated parameter name in '(x x)"))
           (lambda () (parse '{{x x} -> 5})))
(check-equal? (top-interp '5)
              "5")
(check-equal? (top-interp "hello")
              "hello")
(check-equal? (top-interp 'true)
              "true")
(check-equal? (top-interp 'false)
              "false")
(check-equal? (serialize (StringV "hello"))
              "hello")
(check-equal? (serialize (ClosV '(a b) (NumC 5) empty))
              "#<procedure>")
(check-equal? (serialize (PrimOpV '+))
              "#<primop>")
(check-equal? (serialize (NumV 4))
              "4")
(check-equal? (serialize (BoolV #t))
              "true")
(check-equal? (serialize (BoolV #f))
              "false")
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '+) (list (NumC 1) (IdC 'x)))) (list (NumC 5))) top-env)
              (NumV 6)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '-) (list (IdC 'x) (NumC 1)))) (list (NumC 5))) top-env)
              (NumV 4)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '*) (list (IdC 'x) (NumC 2)))) (list (NumC 5))) top-env)
              (NumV 10)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '/) (list (IdC 'x) (NumC 2)))) (list (NumC 6))) top-env)
              (NumV 3)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '<=) (list (IdC 'x) (NumC 2)))) (list (NumC 0))) top-env)
              (BoolV #t)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '<=) (list (IdC 'x) (NumC 2)))) (list (NumC 6))) top-env)
              (BoolV #f)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC 'equal?) (list (IdC 'x) (NumC 2)))) (list (NumC 2))) top-env)
              (BoolV #t)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC 'equal?) (list (IdC 'x) (NumC 2)))) (list (NumC 6))) top-env)
              (BoolV #f)
              )
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC 'equal?) (list (IdC 'x) (NumC 2)))) (list (StringC "yo"))) top-env)
              (BoolV #f)
              )
(check-equal? (parse '{{x} -> 5})
              (LamC '(x) (NumC 5))
              )
(check-equal? (parse '{{x} -> x})
              (LamC '(x) (IdC 'x))
              )
(check-equal? (parse '{{x} -> "hey"})
              (LamC '(x) (StringC "hey"))
              )
(check-equal? (parse '{{x} -> {+ 1 x}})
              (LamC '(x) (AppC (IdC '+) (list (NumC 1) (IdC 'x))))
              )
(check-equal? (parse '{{{x} -> {+ 1 x}} 5})
              (AppC (LamC '(x) (AppC (IdC '+) (list (NumC 1) (IdC 'x)))) (list (NumC 5)))
              )


