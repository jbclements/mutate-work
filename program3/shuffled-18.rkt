#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)
(define-syntax tstruct
    (syntax-rules ()
      [(_ name fields)
       (struct name fields #:transparent)]))


;; Type definitions

(define-type ExprC (U NumC IdC StringC IfC LamC AppC))
(tstruct NumC ([n : Real]))
(tstruct IdC ([x : Symbol]))
(tstruct StringC ([str : String]))
(tstruct IfC ([test : ExprC]
              [then : ExprC]
              [else : ExprC]))
(tstruct LamC ([args : (Listof Symbol)]
               [body : ExprC]))
(tstruct AppC ([fun : ExprC]
               [args : (Listof ExprC)]))

(define-type Value (U NumV BoolV StringV PrimopV CloV))
(tstruct NumV ([n : Real]))
(tstruct BoolV ([b : Boolean]))
(tstruct StringV ([str : String]))
(tstruct PrimopV ([op : (-> Value Value Value)]))
(tstruct CloV ([args : (Listof Symbol)]
               [body : ExprC]
               [env : Env]))

(define-type Env (Immutable-HashTable Symbol Value))


;; Main functions

;; parses and evaluates ZNQR3 program
(: top-interp (Sexp -> String))
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))


;; evaluates an expression with environment
(: interp (ExprC Env -> Value))
(define (interp exp env)
  (match exp
    [(NumC n) (NumV n)]
    [(IdC x) (lookup x env)]
    [(StringC str) (StringV str)]
    [(IfC test then else)
     (match (interp test env)
       [(BoolV b)
        (cond
          [b (interp then env)]       ; true
          [else (interp else env)])]  ; false
       [other (error 'ZNQR "test clause not boolean")])]
    [(LamC args body) (CloV args body env)]
    [(AppC fun app-args)
     (match (interp fun env)
       [(PrimopV op)
        (cond
          [(equal? (length app-args) 2)
           (op (interp (first app-args) env)
               (interp (second app-args) env))]
          [else (error 'ZNQR "primitive operation takes two arguments")])]
       [(CloV clo-args body clo-env)
        (cond
          [(equal? (length app-args) (length clo-args))
           (define argvals (map (lambda ([arg : ExprC])
                                  (interp arg env))
                                  app-args))
           (define new-env (extend-env clo-env clo-args argvals))
           (interp body new-env)]
          [else (error 'ZNQR "arity mismatch")])]
       [other (error 'ZNQR "improper application")])]))


;; parses concrete ZNQR3 syntax
(: parse (Sexp -> ExprC))
(define (parse s)
  (match s
    [(? real? n) (NumC n)]
    [(? symbol? x)
     (cond
       [(set-member? reserved x)
        (error 'ZNQR "reserved identifier: ~s" x)]
       [else (IdC x)])]
    [(? string? str) (StringC str)]
    [(list 'if clauses ...)
     (match clauses
       [(list test then else)
        (IfC (parse test)
             (parse then)
             (parse else))]
       [other (error 'ZNQR "if statement requires 3 clauses")])]
    [(list 'var exps ... last)
     (define asgns (cast exps Sexp))
     (AppC (parse (list (get-lhs asgns) '-> last)) ; LamC form
           (get-rhs asgns))]
    [(list (list (? symbol? ids) ...) '-> body)
     (define args (cast ids (Listof Symbol)))
     (cond
       [(check-duplicates args)
        (error 'ZNQR "duplicate identifiers in function header")]
       [(any-reserved? args)
        (error 'ZNQR "reserved identifier in function header")]
       [else
        (LamC args
              (parse body))])]
    [(list fun args ...)
     (AppC (parse fun)
           (map parse args))]))


;; Helper functions

;; returns string representation of a value
(: serialize (Value -> String))
(define (serialize val)
  (match val
    [(NumV n) (~v n)]
    [(BoolV b)
     (cond
       [b "true"]
       [else "false"])]
    [(StringV str) (~v str)]
    [(PrimopV op) "#<primop>"]
    [(CloV args body env) "#<procedure>"]))


;; retrieves binding from environment
(: lookup (Symbol Env -> Value))
(define (lookup id env)
  (cond
    [(hash-has-key? env id)
     (hash-ref env id)]
    [else (error 'ZNQR "unbound identifier ~s" id)]))


;; extends environment given matching lists of symbol-value pairs
(: extend-env (Env (Listof Symbol) (Listof Value) -> Env))
(define (extend-env env syms vals)
  (foldl (lambda ([sym : Symbol]
                  [val : Value]
                  [res-env : Env])
           (hash-set res-env sym val))
         env
         syms
         vals))


;; returns a list of symbols from a list of var assignments (for desugaring)
(: get-lhs (Sexp -> (Listof Symbol)))
(define (get-lhs asgns)
  (match asgns
    ['() '()]
    [(cons fst rst)
     (match fst
       [(list (? symbol? id) '= rhs)
        (cons id (get-lhs rst))]
       [other (error 'ZNQR "not a valid var assignment")])]))


;; returns a list of exprcs from a list of var assignments (for desugaring)
(: get-rhs (Sexp -> (Listof ExprC)))
(define (get-rhs asgns)
  (match asgns
    ['() '()]
    [(cons fst rst)
     (match fst
       [(list (? symbol? id) '= rhs)
        (cons (parse rhs) (get-rhs rst))]
       [other (error 'ZNQR "not a valid var assignment")])]))


;; takes a list of symbols and checks whether any are reserved
(: any-reserved? ((Listof Symbol) -> Boolean))
(define (any-reserved? ids)
  (foldl (lambda ([id : Symbol]
                  [res : Boolean])
           (or (set-member? reserved id) res))
         #f
         ids))


;; adds two numbers
(: val+ (Value Value -> Value))
(define (val+ l r)
  (cond
    [(and (NumV? l) (NumV? r))
     (NumV (+ (NumV-n l) (NumV-n r)))]
    [else (error 'ZNQR "operand not a number")]))


;; subtracts two numbers
(: val- (Value Value -> Value))
(define (val- l r)
  (cond
    [(and (NumV? l) (NumV? r))
     (NumV (- (NumV-n l) (NumV-n r)))]
    [else (error 'ZNQR "operand not a number")]))


;; multiplies two numbers
(: val* (Value Value -> Value))
(define (val* l r)
  (cond
    [(and (NumV? l) (NumV? r))
     (NumV (* (NumV-n l) (NumV-n r)))]
    [else (error 'ZNQR "operand not a number")]))


;; divides two numbers
(: val/ (Value Value -> Value))
(define (val/ l r)
  (cond
    [(and (NumV? l) (NumV? r))
     (cond
       [(equal? (NumV-n r) 0)
        (error 'ZNQR "divide by zero")]
       [else (NumV (/ (NumV-n l) (NumV-n r)))])]
    [else (error 'ZNQR "operand not a number")]))


;; compares two numbers
(: val<= (Value Value -> Value))
(define (val<= l r)
  (cond
    [(and (NumV? l) (NumV? r))
     (BoolV (<= (NumV-n l) (NumV-n r)))]
    [else (error 'ZNQR "operand not a number")]))


;; checks equality of two values
(: val-equal? (Value Value -> Value))
(define (val-equal? l r)
  (BoolV (and (not (or (PrimopV? l)
                       (PrimopV? r)
                       (CloV? l)
                       (CloV? r)))
              (equal? l r))))


;; Global variables

;; reserved symbols
(define reserved (set 'var 'if '-> '=))

;; default environment
(define top-env (make-immutable-hash
                 (list (cons 'true (BoolV #t))
                       (cons 'false (BoolV #f))
                       (cons '+ (PrimopV val+))
                       (cons '- (PrimopV val-))
                       (cons '* (PrimopV val*))
                       (cons '/ (PrimopV val/))
                       (cons '<= (PrimopV val<=))
                       (cons 'equal? (PrimopV val-equal?)))))


;; Test cases

;; top-interp
(define test1 '{{{x} -> {* 2 x}} 5})
(check-equal? (top-interp test1) "10")

(define test2 '{{{{x} -> {{y} -> {+ x y}}} 4} 5})
(check-equal? (top-interp test2) "9")

(define test3 '{{{f} -> {f 5}} {{x} -> {* 2 x}}})
(check-equal? (top-interp test3) "10")

;; interp
(check-equal? (interp (NumC 5) top-env)
              (NumV 5))
(check-equal? (interp (IdC '+) top-env)
              (PrimopV val+))
(check-equal? (interp (IdC 'true) top-env)
              (BoolV #t))
(check-equal? (interp (StringC "stuff") top-env)
              (StringV "stuff"))
(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 4) (NumC 5)))
                           (AppC (IdC '+) (list (NumC 12) (NumC 13)))
                           (StringC "no"))
                      top-env)
              (NumV 25))
(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 5) (NumC 4)))
                           (AppC (IdC '+) (list (NumC 12) (NumC 13)))
                           (StringC "yes"))
                      top-env)
              (StringV "yes"))
(check-exn (regexp (regexp-quote "test clause not boolean"))
           (λ () (interp (IfC (AppC (IdC '*) (list (NumC 5) (NumC 4)))
                              (AppC (IdC '+) (list (NumC 12) (NumC 13)))
                              (StringC "yes"))
                         top-env)))
(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 2) (NumC 2)))
                      top-env)
              (BoolV #t))
(check-exn (regexp (regexp-quote "primitive operation takes two arguments"))
           (λ () (interp (AppC (IdC '*) (list (NumC 5) (NumC 4) (NumC 6)))
                         top-env)))

(check-equal? (interp (LamC '(x) (AppC (IdC '*) (list (NumC 2) (IdC 'x)))) top-env)
              (CloV '(x) (AppC (IdC '*) (list (NumC 2) (IdC 'x))) top-env))
(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '*) (list (NumC 2) (IdC 'x))))
                            (list (NumC 5)))
                      top-env)
              (NumV 10))
(check-exn (regexp (regexp-quote "arity mismatch"))
           (λ () (interp (AppC (LamC '(x) (AppC (IdC '*) (list (NumC 2) (IdC 'x))))
                               (list (NumC 5) (NumC 8)))
                         top-env)))
(check-exn (regexp (regexp-quote "improper application"))
           (λ () (interp (AppC (NumC 3) (list (NumC 4) (NumC 5)))
                         top-env)))

;; parse
(check-equal? (parse '5) (NumC 5))
(check-equal? (parse '"stuff") (StringC "stuff"))
(check-equal? (parse 'x) (IdC 'x))
(check-exn (regexp (regexp-quote "reserved identifier: var"))
           (λ () (parse 'var)))
(check-equal? (parse '{if {- x 5} {+ x 5} x})
              (IfC (AppC (IdC '-) (list (IdC 'x) (NumC 5)))
                   (AppC (IdC '+) (list (IdC 'x) (NumC 5)))
                   (IdC 'x)))
(check-exn (regexp (regexp-quote "if statement requires 3 clauses"))
           (λ () (parse '{if {+ 5 8} 5})))
(check-equal? (parse '{{x y} -> {* x y}})
              (LamC '(x y) (AppC (IdC '*) (list (IdC 'x) (IdC 'y)))))
(check-exn (regexp (regexp-quote "duplicate identifiers in function header"))
           (λ () (parse '{{x x} -> {* x x}})))
(check-exn (regexp (regexp-quote "reserved identifier in function header"))
           (λ () (parse '{{if x} -> {* x x}})))
(check-equal? (parse '{+ 4 5})
              (AppC (IdC '+) (list (NumC 4) (NumC 5))))
(check-equal? (parse '{{{z y} -> {+ z y}}
                       {+ 9 14}
                       98})
              (AppC (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                          (NumC 98))))
(check-equal? (parse '{var {z = {+ 9 14}}
                           {y = 98}
                           {+ z y}})
              (parse '{{{z y} -> {+ z y}}
                       {+ 9 14}
                       98}))

;; serialize
(check-equal? (serialize (NumV 9)) "9")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (StringV "stuff")) "\"stuff\"")
(check-equal? (serialize (PrimopV val+)) "#<primop>")
(check-equal? (serialize (CloV '(x) (AppC (IdC '*) (list (NumC 2) (IdC 'x))) top-env)) "#<procedure>")

;; lookup
(check-equal? (lookup 'true top-env) (BoolV #t))
(check-exn (regexp (regexp-quote "unbound identifier x"))
           (λ () (lookup 'x top-env)))

;; extend-env
(check-equal? (extend-env (make-immutable-hash (list (cons 'a (NumV 0))))
                          '(x y)
                          (list (NumV 5) (BoolV #t)))
              (make-immutable-hash
               (list (cons 'a (NumV 0))
                     (cons 'x (NumV 5))
                     (cons 'y (BoolV #t)))))

;; get-lhs
(check-equal? (get-lhs '()) '())
(check-equal? (get-lhs (list '{x = 5}
                             '{y = 6}))
              '(x y))
(check-exn (regexp (regexp-quote "not a valid var assignment"))
           (λ () (get-lhs '{x + 7})))

;; get-rhs
(check-equal? (get-rhs '()) '())
(check-equal? (get-rhs (list '{x = 5}
                             '{y = 6}))
              (list (NumC 5)
                    (NumC 6)))
(check-exn (regexp (regexp-quote "not a valid var assignment"))
           (λ () (get-rhs '{x + 7})))

;; any-reserved?
(check-equal? (any-reserved? '(a b c)) #f)
(check-equal? (any-reserved? '(+ a b)) #f)
(check-equal? (any-reserved? '(if var x)) #t)

;; val+
(check-equal? (val+ (NumV 4) (NumV 5))
              (NumV 9))
(check-exn (regexp (regexp-quote "operand not a number"))
           (λ () (val+ (BoolV #t) (NumV 6))))

;; val-
(check-equal? (val- (NumV 4) (NumV 5))
              (NumV -1))
(check-exn (regexp (regexp-quote "operand not a number"))
           (λ () (val- (PrimopV val+) (NumV 6))))

;; val*
(check-equal? (val* (NumV 4) (NumV 5))
              (NumV 20))
(check-exn (regexp (regexp-quote "operand not a number"))
           (λ () (val* (BoolV #t) (NumV 6))))

;; val/
(check-equal? (val/ (NumV 6) (NumV 3))
              (NumV 2))
(check-exn (regexp (regexp-quote "divide by zero"))
           (λ () (val/ (NumV 6) (NumV 0))))
(check-exn (regexp (regexp-quote "operand not a number"))
           (λ () (val/ (BoolV #t) (NumV 6))))

;; val<=
(check-equal? (val<= (NumV 2) (NumV -1))
              (BoolV #f))
(check-equal? (val<= (NumV 2) (NumV 5))
              (BoolV #t))
(check-exn (regexp (regexp-quote "operand not a number"))
           (λ () (val<= (BoolV #t) (NumV 6))))

;; val-equal?
(check-equal? (val-equal? (NumV 5) (NumV 5))
              (BoolV #t))
(check-equal? (val-equal? (NumV 5) (NumV 6))
              (BoolV #f))
(check-equal? (val-equal? (BoolV #f) (BoolV #f))
              (BoolV #t))
(check-equal? (val-equal? (NumV 5) (BoolV #t))
              (BoolV #f))
(check-equal? (val-equal? (PrimopV val-) (BoolV #t))
              (BoolV #f))
