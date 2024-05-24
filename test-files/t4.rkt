#lang typed/racket
(require typed/rackunit)

; Full project implemented, all tests passed :)



(define-type ExprC (U numC stringC appC idC lamC ifC))
(struct numC ([n : Real]) #:transparent)
(struct stringC ([x : String]) #:transparent)
(struct ifC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct appC ([function : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct idC ([name : Symbol]) #:transparent)
(struct lamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)

(define-type Environment (Immutable-HashTable Symbol Value))

(define-type Value (U numV cloV boolV primOpV stringV))
(struct numV ([n : Real]) #:transparent)
(struct stringV ([s : String]) #:transparent)
(struct primOpV ([op : Symbol]) #:transparent)
(struct cloV ([params : (Listof Symbol)] [body : ExprC] [env : Environment]) #:transparent)
(struct boolV ([x : Boolean]) #:transparent)

(define topEnv (hash 'true (boolV #t) 'false (boolV #f)
                     '+ (primOpV '+)
                     '- (primOpV '-)
                     '/ (primOpV '/)
                     '* (primOpV '*)
                     'equal? (primOpV 'equal?)
                     '<= (primOpV '<=)
                     'error (primOpV 'error)))

(define primOpArgNum (hash '- 2 '+ 2 '* 2 '/ 2 'equal? 2 '<= 2 'error 1))

(define recognizedIDs (list 'var 'in 'if '=>))

; Evaluates a JILI5 program and yields a result, which is a String
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) topEnv)))

; ExprC is either:
  ; numC or
  ; stringC or
  ; appC or
  ; idC or
  ; ifC
; Environment is a hash set where key=Symbol, value=Value
; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; Interprets the given expression with a given environment, then returns a value
(define (interp [exp : ExprC] [env : Environment]) : Value
  (match exp
    [(appC name args)
      (match (interp name env)
        [(cloV params body cloVEnv)
          (cond
            [(= (length args) (length params))
            (interp body (extend-caller-env args params cloVEnv env))]
            [else (error 'JILI5 "number of args required for ~e does not match number of passed args" name)])]
        [(primOpV op) (eval-primop op args env)]
        [other (error 'JILI5 "~e is not a function" name)])]
    [(ifC test t f)
      (match (interp test env)
        [(boolV x) (cond
                      [x (interp t env)]
                      [else (interp f env)])]
        [other (error 'JILI5 "if test ~e did not return boolean" test)])]
    [(lamC params body)
      (cloV params body env)]
    [(numC x) (numV x)]
    [(stringC x) (stringV x)]
    [(idC var)
      (cond
        [(hash-has-key? env var) (hash-ref env var)]
        [else (error 'JILI5 "variable not in scope: ~e" var)])]))

; ExprC is either:
  ; numC or
  ; stringC or
  ; appC or
  ; idC or
  ; ifC
; Listof ExperC is either:
  ; ExperC or
  ; '()
; Environment is a hash set where key=Symbol, value=Value
; takes appC's (callee's) args and interps them, then extends and returns cloV's (caller) environment
(define (extend-caller-env [args : (Listof ExprC)] [params : (Listof Symbol)]
                           [childEnv : Environment] [parentEnv : Environment]) : Environment
  (match args
    ['() childEnv]
    [(cons arg next)
      (define argVal (interp arg parentEnv))
      (define newEnv (extend-env childEnv (first params) argVal))
      (extend-caller-env next (rest params) newEnv parentEnv)]))

; Environment is a hash set where key=Symbol, value=Value
; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; takes an environment and adds a new kay (param) and value (val), then returns the new hash
(define (extend-env [env : Environment] [param : Symbol] [val : Value]) : Environment
  (hash-set env param val))

; ExprC is either:
  ; numC or
  ; stringC or
  ; appC or
  ; idC or
  ; ifC
; Parse one Sexp into an ExprC
(define (parse [fun-sexps : Sexp]) : ExprC
  (match fun-sexps
    [(? symbol? var)
      (cond ; check to make sure a idC is not a recognized identifier (var, in, if, =>)
        [(member var recognizedIDs) (error 'JILI5 "~e: id cannot be var, in, if, or =>" var)]
        [else (idC var)])]
    [(? real? n) (numC n)]
    [(list (? symbol? args) ... '=> body) ; need to make sure stuff to the left of => are symbols, if not, do appC
      (lamC (parse-lam-args (cast args (Listof Symbol))) (parse body))]
    [(list 'var (? list? vars) 'in body)
     ;;> cast may introduce bugs - for example, if the first thing in var isn't a symbol
      (define params (map (lambda (var) (cast (first (cast var (Listof Sexp))) Symbol)) vars))
      ;;> again, cast may introduce bugs
      (define args (map (lambda (var) (parse (third (cast var (Listof Sexp))))) vars))
      (appC (lamC (parse-lam-args params) (parse body)) args)]
    [(list 'if arg1 arg2 arg3)
      (ifC (parse arg1) (parse arg2) (parse arg3))]
    [(list funct args ...) (appC (parse funct) (map (lambda (arg) (parse arg)) (cast args (Listof Sexp))))]
    [(? string? str) (stringC str)]
    [other (error 'JILI5 "parse expected an Sexp, got ~e" fun-sexps)]))

; Listof Symbol is either:
  ; Symbol or
  ; '()
; parses and handles the arguments of a lambda expression to check if they are valid arguments
(define (parse-lam-args [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons arg rest)
      (cond
        ;;> there's a handy built-in function that checks for duplicates, check it out!
        [(> (count-in-list args arg) 1) (error 'JILI5 "duplicated param: ~e" arg)]
        [(member arg recognizedIDs) (error 'JILI5 "~e: id cannot be var, in, if, or =>" arg)]
        [else (cons arg (parse-lam-args rest))])]))

; ExprC is either:
  ; numC or
  ; stringC or
  ; appC or
  ; idC or
  ; ifC
; Listof Exprc is either:
  ; ExprC or
  ; '()
; Environment is a hash set where key=Symbol, value=Value
; takes an operator, list of arguments, and an evironment and evaluates the primOp
(define (eval-primop [op : Symbol] [args : (Listof ExprC)] [env : Environment]) : Value
  (define expected-argc (hash-ref primOpArgNum op))
  (cond
    [(equal? (length args) expected-argc)
;;> (AUTOCOMMENT) Failing to add types to lambda arguments and instead using a 'cast' can lead to runtime errors.
      (define iargs (map (lambda (arg) (interp (cast arg ExprC) env)) args))
      (match op
        ['+ (prim-plus (first iargs) (second iargs))]
        ['- (prim-minus (first iargs) (second iargs))]
        ['* (prim-mult (first iargs) (second iargs))]
        ['/ (prim-div (first iargs) (second iargs))]
        ['equal? (prim-equal (first iargs) (second iargs))]
        ['<= (prim-leq (first iargs) (second iargs))]
        ['error (prim-error (first iargs))])]
    [else (error 'JILI5 "wrong number of arguments for primOp: ~e" op)]))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; returns a Real if v is a numV, if not, throw a JILI5 error
(define (make-value-number [v : Value]) : Real
  (match v
    [(numV n) n]
    [else (error 'JILI5 "Type mismatch, expected number, got ~e" v)]))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; returns a Boolean if v is a boolV, if not, throw a JILI5 error
(define (make-value-bool [v : Value]) : Boolean
  (match v
    [(boolV n) n]
    [else (error 'JILI5 "Type mismatch, expected bool, got ~e" v)]))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; evaluates + primOp
(define prim-plus (lambda ([l : Value] [r : Value]) : numV
                    (define leftNum (make-value-number l))
                    (define rightNum (make-value-number r))
                    (numV (+ leftNum rightNum))))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; evaluates - primOp
(define prim-minus (lambda ([l : Value] [r : Value]) : numV
                     (define leftNum (make-value-number l))
                     (define rightNum (make-value-number r))
                     (numV (- leftNum rightNum))))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; evaluates * primOp
(define prim-mult (lambda ([l : Value] [r : Value]) : numV
                    (define leftNum (make-value-number l))
                    (define rightNum (make-value-number r))
                    (numV (* leftNum rightNum))))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; evaluates / primOp
(define prim-div (lambda ([l : Value] [r : Value]) : numV
                   (define leftNum (make-value-number l))
                   (define rightNum (make-value-number r))
                   (cond
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
                     [(= rightNum 0) (error 'JILI5 "cannot divide by zero")]
                     [else (numV (/ leftNum rightNum))])))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; evaluates equal? primOp
(define prim-equal (lambda ([l : Value] [r : Value]) : boolV
                     ;;> needs to check if either value is a primop or closure
                     (boolV (equal? l r))))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; evaluates <= primOp
(define prim-leq (lambda ([l : Value] [r : Value]) : boolV
                   (define leftNum (make-value-number l))
                   (define rightNum (make-value-number r))
                   (boolV (cond
                            [(<= leftNum rightNum) #t]
                            [else #f]))))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; raises a user created error
(define prim-error (lambda ([msg : Value]) : Nothing
                     (error 'user-error (serialize msg))))

; returns how many instances of target is in the list
(define (count-in-list [l : (Listof Any)] [target : Any]) : Real
  (match l
    ['() 0]
    [(cons s next)
      (cond
        [(equal? s target) (+ 1 (count-in-list next target))]
        [else (count-in-list next target)])]))

; Value is either:
  ; numV or
  ; stringV or
  ; primOpV or
  ; cloV or
  ; boolV
; serializes a value into a string
(define (serialize [value : Value]) : String
  (match value
    [(cloV _ _ _) "#<procedure>"]
    [(primOpV _) "#<primop>"]
    [(numV n) (~v n)]
    [(stringV str) (~v str)]
    [(boolV x)
      (cond [x "true"]
            [else "false"])]))

; ====================================================================================================================
; ==================================================== Test Cases ====================================================
; ====================================================================================================================

(check-equal? (serialize (boolV true)) "true")
(check-equal? (serialize (boolV false)) "false")
(check-equal? (serialize (numV 5)) "5")
(check-equal? (serialize (cloV '() (idC 'a) topEnv)) "#<procedure>")
(check-equal? (serialize (primOpV '+)) "#<primop>")

(check-equal? (make-value-number (numV 1)) 1)
(check-exn (regexp (regexp-quote "JILI5: Type mismatch, expected number"))
           (lambda () (make-value-number (boolV #t))))

(check-equal? (make-value-bool (boolV #f)) #f)
(check-exn (regexp (regexp-quote "JILI5: Type mismatch, expected bool"))
           (lambda () (make-value-bool (numV 1))))

(check-equal? (prim-plus (numV 1) (numV 4)) (numV 5))
(check-exn (regexp (regexp-quote "JILI5: Type mismatch, expected number"))
           (lambda () (prim-plus (numV 1) (boolV #t))))
(check-equal? (interp (appC (idC '+) (list (numC 555) (numC 2))) topEnv) (numV 557))
(check-equal? (interp (appC (idC '-) (list (numC 10) (numC 2))) topEnv) (numV 8))
(check-equal? (interp (appC (idC '*) (list (numC 1) (numC 2))) topEnv) (numV 2))
(check-equal? (interp (appC (idC '/) (list (numC 2) (numC 2))) topEnv) (numV 1))
(check-exn (regexp (regexp-quote "JILI5: cannot divide by zero"))
           (lambda () (interp (appC (idC '/) (list (numC 2) (numC 0))) topEnv)))
(check-equal? (interp (appC (idC 'equal?) (list (numC 2) (numC 2))) topEnv) (boolV #t))
(check-equal? (interp (appC (idC 'equal?) (list (numC 2) (numC 1))) topEnv) (boolV #f))
(check-equal? (interp (appC (idC 'equal?)
                            (list (numC 2) (appC (idC '<=) (list (numC 1) (numC 2))))) topEnv) (boolV #f))
(check-equal? (interp (appC (idC 'equal?)
                            (list (appC (idC '<=) (list (numC 8) (numC 10)))
                                  (appC (idC '<=) (list (numC 1) (numC 2))))) topEnv) (boolV #t))
(check-equal? (interp (appC (idC 'equal?)
                            (list (appC (idC '<=) (list (numC 18) (numC 10)))
                                  (appC (idC '<=) (list (numC 1) (numC 2))))) topEnv) (boolV #f))
(check-exn (regexp (regexp-quote "JILI5: wrong number of arguments"))
           (lambda () (interp (appC (idC '/) (list (numC 9) (numC 2) (numC 0))) topEnv)))
(check-exn (regexp
    (regexp-quote "JILI5: number of args required for (lamC '(x y) (numC 1)) does not match number of passed args"))
           (lambda () (top-interp '{{x y => 1} 1})))
(check-exn (regexp (regexp-quote "JILI5: (numC 1) is not a function"))
           (lambda () (top-interp '{1 1})))
(check-equal? (top-interp '{if {<= 5 2} 0 2}) "2")
(check-exn (regexp (regexp-quote "if test (numC 3) did not return boolean"))
           (lambda () (top-interp '{if 3 0 2})))
(check-exn (regexp (regexp-quote "parse expected an Sexp"))
           (lambda () (top-interp '())))
(check-equal? (parse '{x => {+ 1 x}}) (lamC '(x) (appC (idC '+) (list (numC 1) (idC 'x)))))
(check-equal? (top-interp '{if true 0 1}) "0")
(check-equal? (top-interp '{if false 0 1}) "1")
(check-equal? (top-interp '{if {<= 1 2} 0 1}) "0")
(check-equal? (top-interp '{if {<= 2 1} 0 1}) "1")
(check-equal?
 (parse '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}})
 (appC (lamC '(z y) (appC (idC '+) (list (idC 'z) (idC 'y))))
       (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))

(check-equal? (top-interp '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}}) "121")
(check-equal? (parse 'true) (idC 'true))
(check-equal? (parse 'false) (idC 'false))
(check-equal? (interp (idC 'true) topEnv) (boolV true))
(check-equal? (interp (idC 'false) topEnv) (boolV false))
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp 'false) "false")
(check-equal? (parse '{+ 1 2}) (appC (idC '+) (list (numC 1) (numC 2))))
(check-equal? (interp (appC (idC '+) (list (numC 1) (numC 2))) topEnv) (numV 3))

(check-exn (regexp (regexp-quote "Type mismatch, expected number"))
           (lambda () (top-interp '{+ + +})))

(define prog10 '{{{x => {y => {+ x y}}} 7} 8})
(define prog10-parse (appC (appC (lamC '(x)(lamC '(y) (appC (idC '+) (list (idC 'x) (idC 'y)))))
                                 (list (numC 7))) (list (numC 8))))
(check-equal? (parse prog10) prog10-parse)
(check-equal? (top-interp prog10) "15")

(define err-var (idC 'gaming))
(check-exn (regexp (regexp-quote "JILI5: variable not in scope: 'gaming"))
           (lambda () (interp err-var topEnv)))

(define err-exp (appC (idC 'hehehe) (list (numC 555) (numC 2))))
(check-exn (regexp (regexp-quote "JILI5: variable not in scope: 'hehehe"))
           (lambda () (interp err-exp topEnv)))


(check-equal? (top-interp '{if true 0 1}) "0")
(check-equal? (top-interp '{if false 0 1}) "1")
(check-equal? (top-interp '{if {<= 1 2} 0 1}) "0")
(check-equal? (top-interp '{if {<= 2 1} 0 1}) "1")
(check-equal? (top-interp '{if {equal? 1 1} 0 1}) "0")
(check-equal? (top-interp '{if {equal? 0 1} 0 1}) "1")
(check-equal? (top-interp '{if {equal? "yes" "no"} "true" "false"}) "\"false\"")
(check-equal? (top-interp '{if {equal? "yes" "yes"} "true" "false"}) "\"true\"")
(check-equal? (top-interp '{if {equal? true false} "true" "false"}) "\"false\"")
(check-equal? (top-interp '{if {equal? true true} "true" "false"}) "\"true\"")
(check-equal? (top-interp '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}}) "121")
(check-equal? (top-interp '{{{x => {y => {+ x y}}} 7} 8}) "15")
(check-equal? (top-interp '{{{x => {y => {- x y}}} 7} 8}) "-1")
(check-equal? (top-interp '{{{x => {y => {* x y}}} 7} 8}) "56")
(check-equal? (top-interp '{{{x => {y => {/ x y}}} 8} 8}) "1")
(check-equal? (top-interp '{x => {y => {/ x y}}}) "#<procedure>")
(check-equal? (top-interp '{+ 1 2}) "3")
(check-equal? (top-interp '{{x y => 2} 3 4}) "2")
(check-equal? (top-interp '((+ => (* + +)) 14)) "196")
(check-exn (regexp (regexp-quote "user-error: \"this is an error\""))
;;> (AUTOCOMMENT) Grader: most of these are errors, but be sure to check whether this message is warranted:
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
           (lambda () (top-interp '(error "this is an error"))))
(check-equal? (parse '"true") (stringC "true"))
(check-exn (regexp (regexp-quote "JILI5: 'var: id cannot be var, in, if, or =>"))
           (lambda () (parse '{+ var 1})))
(check-exn (regexp (regexp-quote "JILI5: 'in: id cannot be var, in, if, or =>"))
           (lambda () (parse '{+ in 1})))
(check-exn (regexp (regexp-quote "JILI5: 'if: id cannot be var, in, if, or =>"))
           (lambda () (parse '{+ if 1})))

(check-exn (regexp (regexp-quote "JILI5: duplicated param: 'x"))
           (lambda () (parse '{x x => 1})))

(check-exn (regexp (regexp-quote "JILI5: '=>: id cannot be var, in, if, or =>"))
           (lambda () (parse '{3 4 5 => 1})))

(check-equal? (top-interp '(((a x y => (w => (+ x (w y)))) 1 2 3) (b => 1))) "3")
(check-equal?
 (top-interp '(if (equal? (((a x y => (w => (+ x ((((w y))))))) 1 2 3) (b => (=> (=> (=> 1))))) 3) true false)) "true")

(check-exn (regexp (regexp-quote "JILI5: 'in: id cannot be var, in, if, or =>"))
           (lambda () (parse-lam-args '(in))))
