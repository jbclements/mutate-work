#lang typed/racket

;;> eyeball: 5/6, Mostly good, see comments

(require typed/rackunit)

; Binding Definitions
(struct Binding ((name : Symbol) (val : Value)) #:transparent)

; Environment Definitions
(define-type Env (Listof Binding))
(define mt-env '())
(define extend-env cons)


; ExprC Definitions
(define-type ExprC (U ifC AppC IdC NumC LamC BoolC StringC))
(struct BoolC ([b : Boolean]) #:transparent)
(struct ifC ([exp : ExprC] [l : ExprC] [r : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct IdC ([sym : Symbol]) #:transparent)
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct LamC ([arg : (Listof Symbol)] [body : ExprC]) #:transparent)

; Value Definitions
(define-type Value (U NumV BoolV CloV PrimV StringV))
(struct NumV ([n : Real]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct CloV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([operator : (Value Value -> Value)]) #:transparent)

; (top-interp fun-sexps) → Real
; fun-sexps : s-expression
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; (parse s) → ExprC
; s : s-expression
; Parses an expression.
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? s) (NumC s)]
    ;;> more useful error messages would help decoding
    [(? symbol? s) (if (sym-check s) (IdC s) (error 'parse "ZNQR: invalid input"))]
    [(? string? s) (StringC s)]
    [(list 'if exp l r) (ifC (parse exp) (parse l) (parse r))]
    [(list 'if exp l r ...) (error 'parse "ZNQR: invalid input")]
    [(list 'var id ... body)
     (AppC
      (LamC (dup-check (app-help-3 (cast id (Listof Sexp)))) (parse body))
      (app-help-4 (cast id (Listof Sexp))))]
    [(list (list id ...) '-> body) (LamC (dup-check (app-help-2 id)) (parse body))]
    ;;> this isnt an error
    [(list (? real? num) args ...) (error 'parse "ZNQR: invalid input")] 
    [(list name args ...) (AppC (parse name) (app-help args))]
    ))

; (interp exp funs) → Real
; exp : ExprC
; funs : (listof FundefC)
; Interprets the given expression, using the list of funs to resolve applications.
(define (interp [e : ExprC] [env : Env]) : Value
      (match e
        [(NumC n) (NumV n)]
        [(IdC id) (lookup id env)]
        [(BoolC b) (BoolV b)]
        [(StringC s) (StringV s)]
        [(LamC a b) (CloV a b env)]
        [(ifC exp l r) (match (interp exp env)
                         [(BoolV b) (cond
                            [b (interp l env)]
                            [else (interp r env)])]
                         [else (error 'interp "ZNQR: conditional does not evaluate to a boolean")])]
        [(AppC f a)
         (match (interp f env)
           [(PrimV op) (prim-handler op (interp-help a env))]
           [(CloV param body clo-env)
            (define new-env (extend-env-helper clo-env param (interp-help a env)))
              (interp body new-env)]
           [else (error 'interp "ZNQR: lengths don't match")])]
        ))


; takes a Value and returns a string
(define (serialize [v : Value]) : String
  (match v
    [(BoolV b) (if b "true" "false")]
    [(StringV s) s]
    [(NumV n) "~v" (number->string n)]
    [(CloV args body env) "#<procedure>"]
    [(PrimV op) "#<primop>"]))

; helper for extend-env-helper
(define (extend-env-helper [clo-env : Env] [names : (Listof Symbol)] [vals : (Listof Value)]) : Env
  (cond
    [(not (equal? (length names) (length vals))) (error 'extend-env-helper "ZNQR: invalid number of args provided")]
    [(empty? names) clo-env]
    [else (extend-env-helper (extend-env (Binding (first names) (first vals)) clo-env) (rest names) (rest vals))])
  )

; duplicate checker
(define (dup-check [ids : (Listof Symbol)]) : (Listof Symbol)
  (if
   (equal? (length ids) (length (remove-duplicates ids)))
   ids
    (error 'dup-check "ZNQR: duplicate variable declarations")))


; primitive operator functions
(define (prim+ [l : Value] [r : Value]) : Value
  (match l
    [(NumV n) (match r
                [(NumV n2) (NumV (+ n n2))]
                [else (error 'prim+ "ZNQR: at least one argument was not a number")])]
    [else (error 'prim+ "ZNQR: at least one argument was not a number")]))



(define (prim- [l : Value] [r : Value]) : Value
  (match l
    [(NumV n) (match r
                [(NumV n2) (NumV (- n n2))]
                [else (error 'prim- "ZNQR: at least one argument was not a number")])]
    [else (error 'prim- "ZNQR: at least one argument was not a number")]))



(define (prim/ [l : Value] [r : Value]) : Value
  (match l
    [(NumV n) (match r
                [(NumV n2) (if (equal? 0 n2) (error 'prim/ "ZNQR: divide by zero") (NumV (/ n n2)))]
                [else (error 'prim/ "ZNQR: at least one argument was not a number")])]
    [else (error 'prim/ "ZNQR: at least one argument was not a number")]))



(define (prim* [l : Value] [r : Value]) : Value
  (match l
    [(NumV n) (match r
                [(NumV n2) (NumV (* n n2))]
                [else (error 'prim* "ZNQR: at least one argument was not a number")])]
    [else (error 'prim* "ZNQR: at least one argument was not a number")]))



(define (prim<= [l : Value] [r : Value]) : Value
  (match l
    [(NumV n) (match r
                [(NumV n2) (BoolV (<= n n2))]
                [else (error 'prim<= "ZNQR: at least one argument was not a number")])]
    [else (error 'prim<= "ZNQR: at least one argument was not a number")]))



(define (prim= [l : Value] [r : Value]) : Value
  (if (equal? l r) (BoolV true) (BoolV false)))



; top-level environment
(define top-env (list (Binding 'true (BoolV true))
                      (Binding 'false (BoolV false))
                      (Binding '+ (PrimV prim+))
                      (Binding '- (PrimV prim-))
                      (Binding '/ (PrimV prim/))
                      (Binding '* (PrimV prim*))
                      (Binding '<= (PrimV prim<=))
                      (Binding 'equal? (PrimV prim=))))

; app-help: helps to process 0-n args
(define (app-help [ses : (Listof Sexp)]): (Listof ExprC)
  (cond
    [(empty? ses) '()]
    [else (cons (parse (first ses)) (app-help (rest ses)))]))

; helper: makes sure user doesnt supply invalid symbol as variable name
(define (sym-check [sym : Symbol]) : Boolean
  (match sym
    ['if #f]
    ['var #f]
    ['-> #f]
    ['= #f]
    [else #t]))

;parse-b and app-help 2 are used to get symbols for LamC
; (parse s) → ExprC
; s : s-expression
; Parses an expression.
(define (parse-b [s : Sexp]) : Symbol
  (match s
    [(? real? s) (error 'parse-b "ZNQR: invalid input")]
    [(? symbol? s) (if (sym-check s) s (error 'parse-b "ZNQR: invalid input"))]
    [(? string? s) (error 'parse-b "ZNQR: invalid input")]
    ))


; app-help-2: helps to process 0-n args
(define (app-help-2 [ses : (Listof Sexp)]): (Listof Symbol)
  (cond
    [(empty? ses) '()]
    [else (cons (parse-b (first ses)) (app-help-2 (rest ses)))]))

; app-help-3: helps to process 0-n args
(define (app-help-3 [ses : (Listof Sexp)]): (Listof Symbol)
  (cond
    [(empty? ses) '()]
    [else (match (first ses)
            [(list sym '= val) (cons (parse-b sym) (app-help-3 (rest ses)))])
     ]))

; app-help-3: helps to process 0-n args
(define (app-help-4 [ses : (Listof Sexp)]): (Listof ExprC)
  (cond
    [(empty? ses) '()]
    [else (match (first ses)
            [(list sym '= val) (cons (parse val) (app-help-4 (rest ses)))])
     ]))

; lookup: (Symbol Env -> Real) finds the value of the symbol
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "ZNQR: name not found")]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (Binding-val (first env))]
            [else (lookup for (rest env))])]))



; handler for prim ops
(define (prim-handler [op : (Value Value -> Value)] [args : (Listof Value)]) : Value
  (match args
    [(list l r) (op l r)]
    [else (error 'prim-handler "ZNQR: expected 2 arguments")]))


; check-equal: dup-check
(check-equal? (dup-check (list 'a 'b 'c)) (list 'a 'b 'c))
(check-exn (regexp (regexp-quote "ZNQR: duplicate variable declarations"))
           (lambda () (dup-check (list 'a 'a 'b))))

; check-equal: extend-env-helper
(check-exn (regexp (regexp-quote "ZNQR: invalid number of args provided"))
           (lambda () (extend-env-helper mt-env (list 'a 'b) (list (NumV 2)))))

; check-equal: prim*
(check-equal? (prim+ (NumV 3) (NumV 4)) (NumV 7))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim+ (BoolV true) (NumV 4))))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim+ (NumV 4) (BoolV true))))

(check-equal? (prim- (NumV 3) (NumV 4)) (NumV -1))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim- (BoolV true) (NumV 4))))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim- (NumV 4) (BoolV true))))

(check-equal? (prim/ (NumV 3) (NumV 3)) (NumV 1))
(check-exn (regexp (regexp-quote "ZNQR: divide by zero"))
           (lambda () (prim/ (NumV 3) (NumV 0))))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim/ (BoolV true) (NumV 4))))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim/ (NumV 4) (BoolV true))))

(check-equal? (prim* (NumV 3) (NumV 4)) (NumV 12))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim* (BoolV true) (NumV 4))))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim* (NumV 4) (BoolV true))))

(check-equal? (prim<= (NumV 3) (NumV 4)) (BoolV true))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim<= (BoolV true) (NumV 4))))
(check-exn (regexp (regexp-quote "ZNQR: at least one argument was not a number"))
           (lambda () (prim<= (NumV 4) (BoolV true))))

(check-equal? (prim= (NumV 4) (NumV 4)) (BoolV true))
(check-equal? (prim= (BoolV false) (NumV 4)) (BoolV false))

; check-equal: parse-b
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse-b '=)))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse-b 5)))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse-b "hello")))

; check-equal: parse
(check-equal? (parse 5) (NumC 5))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse "hello") (StringC "hello"))
(check-equal? (parse '{if true 4 "hello"}) (ifC (IdC 'true) (NumC 4) (StringC "hello")))
(check-equal? (parse '{{a b} -> {+ a b}})
              (LamC (list 'a 'b)
                    (AppC (IdC '+) (list (IdC 'a) (IdC'b)))))
(check-equal? (parse '{{{z y} -> {+ z y}}
                       {+ 9 14}
                       98}) (AppC (LamC (list 'z 'y)
                    (AppC (IdC '+) (list (IdC 'z) (IdC'y))))
                                  (list
                                   (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                                   (NumC 98))
                                  ))
(check-equal? (parse '{var {z = {+ 9 14}}
                           {y = 98}
                           {+ z y}}) (AppC (LamC (list 'z 'y)
                    (AppC (IdC '+) (list (IdC 'z) (IdC'y))))
                                  (list
                                   (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                                   (NumC 98))
                                  ))

(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse '{if true 2 3 4})))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse '=)))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse 'if)))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse 'var)))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse '->)))
(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (parse '->)))

; check-equal: lookup
(check-equal? (lookup 'a (list (Binding 'c (NumV 5)) (Binding 'b (NumV 4)) (Binding 'a (NumV 3)))) (NumV 3))
(check-exn (regexp (regexp-quote "ZNQR: name not found"))
           (lambda () (lookup 'd (list (Binding 'c (NumV 5)) (Binding 'b (NumV 4)) (Binding 'a (NumV 3))))))

; check-equal: prim-handler
(check-exn (regexp (regexp-quote "ZNQR: expected 2 arguments"))
           (lambda () (prim-handler prim+ (list (NumV 3) (NumV 3) (NumV 3)))))

; check-equal: interp-help
(define (interp-help [args : (Listof ExprC)] [env : Env]) : (Listof Value)
  (match args
    [(? empty? s) '()]
    [(list first rest ...) (cons (interp first env) (interp-help rest env))]))

; check-equal: interp
(check-equal? (interp (StringC "hello") top-env) (StringV "hello"))
(check-equal? (interp (AppC (IdC '+) (list (NumC 2) (NumC 2))) top-env) (NumV 4))
(check-equal? (interp (AppC (LamC (list 'x 'y) (AppC (IdC '-) (list (IdC 'x) (IdC 'y))))
                            (list (NumC 2) (NumC 2))) top-env) (NumV 0))
(check-equal? (interp (ifC (BoolC true) (NumC 4) (NumC 5)) top-env) (NumV 4))
(check-equal? (interp (ifC (BoolC false) (NumC 4) (NumC 5)) top-env) (NumV 5))
(check-exn (regexp (regexp-quote "ZNQR: conditional does not evaluate to a boolean"))
           (lambda () (interp (ifC (NumC 4) (NumC 4) (NumC 5)) top-env)))

; check-equal: serialize
(check-equal? (serialize (NumV 5)) "5")
(check-equal? (serialize (StringV "hello")) "hello")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV false)) "false")
(check-equal? (serialize (CloV (list 'a 'b) (AppC (IdC '+) (list (IdC 'a) (IdC 'b))) '())) "#<procedure>")
(check-equal? (serialize (PrimV prim+)) "#<primop>")

; check-equal: top-interp
(check-equal? (top-interp '{var {z = {+ 9 14}}
      {y = 98}
  {+ z y}}) "121")

(check-exn (regexp (regexp-quote "ZNQR: invalid input"))
           (lambda () (top-interp '(3 4 5))))
(check-exn (regexp (regexp-quote "ZNQR: lengths don't match"))
           (lambda () (top-interp '(((() -> 3)) 4 5))))



