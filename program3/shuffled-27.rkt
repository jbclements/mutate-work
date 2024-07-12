#lang typed/racket

;;> eyeball: 2/6, Good start, see comments

(require typed/rackunit)

; I got everything to work aside from Parsing as well as its testing as well as local variables. The error handling for
; Parsing is set up and tested

; ValueV Data Definition
(define-type ValueV (U NumV BoolV ClosV FunV PrimV StringV ClosV))
(struct NumV ([value : Real]) #:transparent)
(struct BoolV ([value : Boolean]) #:transparent)
(struct FunV ( [arg : (Listof Symbol)] [body : ExprC]))
(struct StringV ([value : String]) #:transparent)
(struct PrimV ([operator : (ValueV ValueV -> ValueV)]) #:transparent)
(struct ClosV ([arg : (Listof Symbol)] [body : ExprC] [env : Environment]) #:transparent)

; Binding and Environment Data Definition
(struct Binding ((name : Symbol) (val : ValueV)) #:transparent)
(define-type Environment (Listof Binding))

; ExprC Structs Definition
(define-type ExprC (U NumC IfC IdC AppC FundefC StringC LamC)) ; and local Variable C
(struct NumC ([n : Real]) #:transparent)
(struct StringC ([n : String]) #:transparent)
(struct IfC([value : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)]) #:transparent)
(struct LamC ([arg : (Listof Symbol)] [body : ExprC]))
(struct LocalC ([var : Symbol] [value : ExprC]) #:transparent)
(struct FundefC ([arg : (Listof Symbol)] [body : ExprC]) #:transparent)

; Top-Level Environment
(define environ (list
             (Binding '+ (PrimV (lambda (x y) (BinOp + x y))))
                  (Binding '- (PrimV  (lambda (x y) (BinOp - x y))))
                  (Binding '/ (PrimV (lambda (x y) (BinOp / x y)) ))
                  (Binding '* (PrimV (lambda (x y) (BinOp * x y))))
                  (Binding 'equal? (PrimV (lambda (x y) (my-equal x y))))
                  (Binding '<= (PrimV (lambda (x y) (Compare <= x y))))
                  (Binding 'true (BoolV #t))
                  (Binding 'false (BoolV #f))))

; Given Code
; Given Sexp for Functions, evaluates it
(define (top-interp [s : Sexp]) : String
  "TODO - Parse"
  ;(serialize (interp (parse s) environ))
)

; Given an Sexp, Return the evaluation of it in ZNQR
(define (interp [exp : ExprC] [env : Environment]) : ValueV
  (match exp
    [(NumC s) (NumV s)]
    [(StringC s) (StringV s)]
    [(LamC a b) (ClosV a b env)]
    ;[(LocalC sym body) ()] ; Have to add the local variable to environment and continue
    [(IfC value then else) (define testExpr (interp value env))
                           (cond
                             [(BoolV? testExpr) (cond
                                                  [(equal? (BoolV #t) testExpr) (interp then env)]
                                                  [else (interp else env)])]
                             [else (error "ZNQR: Interp - IfC's Value is not evaluating to a Boolean")])]
    [(IdC x) (lookup x env)]
    [(AppC f a) (match (interp f env)
                  [(PrimV op) (cast a (Listof ExprC))
                   (cond
                     [(empty? a) (error "ZNQR: Interp - Not Enough Values for Operation")]
                     [else (prim-handler op (interp (first a) env)
                                         (cond
                                           [(empty? (rest (rest a))) (interp (first (rest a)) env)]
                                           [else (error "ZNQR: More than 2 Values Given for a Binary Option")]))])]
                  [(ClosV param body clo-env) (define new-env (full-extend param clo-env a))
                                             (interp body new-env)]
                  [(FunV arg body) (interp body (full-extend arg env a))])]
    ;;> no fundef's in interp
    [(FundefC a b) (FunV a b)]))

; Given an Sexp, Convert to ExprC
; TODO
(define (parse [s : Sexp] ) : ExprC
  (match s
    [ (? real?) (NumC s)]
    [ (? string?) (StringC s)]
    [ (list 'if value then else) (IfC (parse value) (parse then) (parse else))]
    [ (list 'if a ...) (error "ZNQR: If statement without both a then or else")]
    ;[ (list a b ... -> c) (NumC 5)] ; AppC
    ;[ (list (? Symbol p) ...) (NumC 4)] ; FundefC
    ;[ (list 'var a b ... c) ;Local Variable
    [(? symbol?) (IdC s)]))
    ;[ else (error "ZNQR: Undesired Input")]))


; Given a symbol, find its corresponding Value in the list
(define (lookup [n : Symbol] [env : Environment]) :  ValueV
  (cond
    [(empty? env)
     (error "ZNQR: Get-Bind - Lookup - reference to undefined function")]
    [(cons? env)
     (cond
       [(equal? n (Binding-name (first env))) (Binding-val (first env))]
       [else (lookup n (rest env))])]))

; Evaluates Primitive Operand
(define (prim-handler [op : (ValueV ValueV -> ValueV)] [expr : ValueV] [expr2 : ValueV])
  (op expr expr2))

; Adds a binding to the environment
(define (extend-env [environ : Environment] [item : Binding]) : Environment
  (append environ (list item)))

; Helps add all parameters and its values to the Environment
(define (full-extend [funArg : (Listof Symbol)] [env : Environment] [arg : (Listof ExprC)]) : Environment
  (cond
    [(empty? funArg) env]
    [else (cast funArg (Listof Symbol))(cast arg (Listof ExprC))
          (full-extend (rest funArg) (extend-env env (Binding (first funArg) (interp (first arg) env))) (rest arg))]))

; Given a ValueV, Serialize it
(define (serialize [value : ValueV]) : String
  (match value
    [(PrimV n) "#<primop>"]
    [(ClosV a b c) "#<procedure>"]
    [(BoolV n) (cond
                 [(equal? n #t) "true"]
                 [else "false"])]
    [(StringV n) (~v n)]
    [(NumV n) (~v n)]))


; Support Function for Primitive Operations
; Given 2 ValueVs, Perform a Binary Operation them
(define (BinOp [func : (Real Real -> Real)] [l : ValueV] [r : ValueV]) : ValueV
  (cond
    [(and (NumV? l) (NumV? r)) (cond
                                 [(and (equal? / func) (zero? (NumV-value r))) (error "ZNQR: Cannot Divide by Zero")]
                                 [else (NumV (func (NumV-value l) (NumV-value r)))])]
    [else (error "ZNQR: BinOp - one argument was not a number")]))

; Support Function for Primitive Operations
; Given 2 ValueVs, Compare them
(define (Compare [func : (Real Real -> Boolean)] [l : ValueV] [r : ValueV]) : ValueV
  (cond
    [(and (NumV? l) (NumV? r))  (BoolV (func (NumV-value l) (NumV-value r)))]
    [else (error "ZNQR: Compare - one argument was not a number")]))

; Support Function for Primitive Operations
; Given 2 ValueVs, check if they are equal
(define (my-equal [l : ValueV] [r : ValueV]) : ValueV
  (cond
    [(or (PrimV? l) (PrimV? r) (ClosV? l) (ClosV? r)) (BoolV #f)]
    [else (BoolV (equal? l r))]))

; Support Function for Parse - Used to Help Detect Errors
; Given a list, checks if an element shows up more than once
(define (appears-once [list : (Listof Symbol)]) : Boolean
  (cond
    [(empty? list) #t]
    [(equal? 0 (check-additional-amount (rest list) (first list) 0)) (appears-once (rest list))]
    [else #f]))

; Support Function for appears-once
; Gets the number of time the passed word shows up
(define (check-additional-amount [list : (Listof Symbol)] [key : Symbol] [count : Real]) : Real
  (cond
    [(empty? list) count]
    [(equal? (first list) key) (check-additional-amount (rest list) key (+ 1 count))]
    [else (check-additional-amount (rest list) key count)]))

; Support Function for Parse - Used to help Detect Errors
; Returns True if is a binop/if operation, false otherwise
(define (isBinop [a : Symbol]) : Boolean
  (cond
    [(not (member a '(+ / - * if))) #f]
    [else #t]))

; Support Function for Parse - Used to help Detect Errors
; Returns True if is a binop/if operation, false otherwise
(define (isId [a : Symbol]) : Boolean
  (cond
    [(not (member a '(var if -> =))) #t]
    [else #f]))

; -------------------------- TEST CASES --------------------------

; Top-interp Test Cases
; Interp - ExprC + Functions Test Cases
(check-equal? (interp (NumC 5) environ) (NumV 5))
(check-equal? (interp (AppC (IdC '+) (list (NumC 4) (NumC 5))) environ) (NumV 9))
(check-equal?  (interp (AppC (IdC '<=) (list (NumC 4) (NumC 5))) environ) (BoolV #t))
(check-equal?  (interp (AppC (IdC 'equal?) (list (NumC 4) (NumC 5))) environ) (BoolV #f))
(check-equal?  (interp (LamC '(a) (NumC 5)) environ) (ClosV '(a) (NumC 5) environ))
(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 4) (NumC 4))) (NumC 5) (NumC 6)) environ) (NumV 5))
(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 4) (NumC 3))) (NumC 5) (NumC 6)) environ) (NumV 6))

(check-equal? (interp (AppC (IdC '+) (list (NumC 10) (AppC (FundefC '(_) (NumC 5)) (list (NumC 10))))) environ)
              (NumV 15))
(check-exn (regexp (regexp-quote "ZNQR: More than 2 Values Given for a Binary Option"))
           (lambda () (interp (AppC (IdC '+) (list (NumC 4) (NumC 5) (NumC 6))) environ)))
(check-exn (regexp (regexp-quote "ZNQR: Interp - Not Enough Values for Operation"))
           (lambda () (interp (AppC (IdC '+) '()) environ)))


;Interp Test Cases
(check-equal? (interp (NumC 5) environ) (NumV 5))
(check-equal? (interp (StringC "hello") environ) (StringV "hello"))
(check-equal? ((PrimV-operator (cast (interp (IdC '+) environ) PrimV)) (NumV 5) (NumV 5)) (NumV 10))
(check-equal? (interp (AppC (LamC '(a b) (AppC (IdC '+) (list (IdC 'a) (IdC 'b)))) (list (NumC 5) (NumC 4))) environ)
              (NumV 9))
(check-exn (regexp (regexp-quote "ZNQR: Interp - IfC's Value is not evaluating to a Boolean"))
           (lambda () (interp (IfC (NumC 3) (NumC 5) (NumC 3)) environ)))



; Primitive Operations
(check-equal? ((PrimV-operator (cast (lookup '/ environ) PrimV)) (NumV 4) (NumV 4)) (NumV 1))
(check-equal? ((PrimV-operator (cast (lookup '* environ) PrimV)) (NumV 4) (NumV 4)) (NumV 16))
(check-equal? ((PrimV-operator (cast (lookup '+ environ) PrimV)) (NumV 4) (NumV 4)) (NumV 8))
(check-equal? ((PrimV-operator (cast (lookup '- environ) PrimV)) (NumV 4) (NumV 4)) (NumV 0))
(check-equal? ((PrimV-operator (cast (lookup 'equal? environ) PrimV)) (NumV 4) (ClosV '(a) (NumC 5) environ))
              (BoolV #f))
(check-exn (regexp (regexp-quote "ZNQR: Cannot Divide by Zero"))
           (lambda () ((PrimV-operator (cast (lookup '/ environ) PrimV)) (NumV 4) (NumV 0))))
(check-exn (regexp (regexp-quote "ZNQR: BinOp - one argument was not a number"))
           (lambda () ((PrimV-operator (cast (lookup '/ environ) PrimV)) (BoolV #t) (NumV 0))))
(check-exn (regexp (regexp-quote "ZNQR: Compare - one argument was not a number"))
           (lambda () ((PrimV-operator (cast (lookup '<= environ) PrimV)) (BoolV #t) (NumV 0))))
(check-exn (regexp (regexp-quote "ZNQR: Get-Bind - Lookup - reference to undefined function"))
           (lambda () (lookup 'ab environ)))

; Extend-Env Test Cases
(check-equal? (extend-env '() (Binding 'a (NumV 5))) (list (Binding 'a (NumV 5))))
(check-equal? (extend-env environ (Binding 'a (NumV 5))) (append environ (list (Binding 'a (NumV 5)))))


; Parse - SExp -> ExprC Test Cases
(check-equal? (parse '5) (NumC 5))
(check-equal? (parse '+) (IdC '+))
(check-equal? (parse "Hello") (StringC "Hello"))
(check-equal? (parse '(if 4 5 6)) (IfC (NumC 4) (NumC 5) (NumC 6)))
; More IfC needed when AppC works for the value of if
(check-exn (regexp (regexp-quote "ZNQR: If statement without both a then or else"))
           (lambda () (parse '(if 5 6))))

; More Cases Needed Here

; Serialize Test Cases
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (StringV "test")) "\"test\"")
(check-equal? (serialize (NumV 5)) "5")
(check-equal? (serialize (lookup '+ environ)) "#<primop>")
(check-equal? (serialize (ClosV '(a) (NumC 5) environ)) "#<procedure>")

; Appears Once Test Cases
(check-equal? (appears-once '(a a)) #f)
(check-equal? (appears-once '(a b c)) #t)

; Check-additional-amount Test Cases
(check-equal? (check-additional-amount '(a b c) 'd 0) 0)
(check-equal? (check-additional-amount '(a b c) 'a 0) 1)
(check-equal? (check-additional-amount '(a c c) 'c 0) 2)

; Is-Fail / Is-Id Test Cases
(check-equal? (isBinop '+) #t)
(check-equal? (isBinop 'a) #f)
(check-equal? (isId '+) #t)
(check-equal? (isId 'if) #f)

; Top-Interp
(check-equal? (top-interp 'anything) "TODO - Parse")

