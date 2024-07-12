#lang typed/racket
(require typed/rackunit)

;;> eyeball: 2/6, yes, it's assignment 2.  Many thanks for the comment.

;________________________________________________________________________
;
;ASSIGNMENT 2
;________________________________________________________________________
;Hello! This is my assignment #2 from last quarter, including eager substitution!
;
;________________________________________________________________________
;Type Definitions

(define-type ExprC (U NumC IdC AppC PlusC MultC ifleq0 BinopC))
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : Symbol] [arg : (Listof ExprC)]) #:transparent)
(struct PlusC ([l : ExprC] [r : ExprC]) #:transparent)
(struct MultC ([l : ExprC] [r : ExprC]) #:transparent)
(struct ifleq0 ([iff : ExprC] [thenn : ExprC] [elsee : ExprC]) #:transparent)
(struct BinopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)

(struct FunDefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)

;define the binary operators our language supports
(define binaryOps (hash '+ + '- - '* * '/ /))

;____________________________________
;Function Definitions

;____________________________________
;Parser

;Parses an expression.
(: parse (-> Sexp ExprC))
(define (parse s)
  (match s
    [(list 'ifleq0 iff thenn elsee) (ifleq0 (parse iff) (parse thenn) (parse elsee))]
    [(list (? symbol? sym) l r)
     ;check if the bianry operator exists in our table. if not, its an AppC with 2 args
     (cond [(hash-has-key? binaryOps sym)  (BinopC sym (parse (second s)) (parse (third s)))]
           [(symbol=? sym 'ifleq0) (error 'parse "ZNQR: if-then-else takes exactly 3 args")]
           [(symbol=? sym 'func) (error 'parse "ZNQR: can't define functions inside expressions")]
           [else (AppC sym (map parse (list l r)))])]
    [(list (? symbol? fun) rst ...)
     (cond [(hash-has-key? binaryOps fun) (error 'parse "ZNQR: Binary Operations take exactly 2 args")]
           [(symbol=? fun 'ifleq0) (error 'parse "ZNQR: if-then-else takes exactly 3 args")]
           [(symbol=? fun 'func) (error 'parse "ZNQR: can't define functions inside expressions")]
           [else (AppC fun (map parse rst))])]
    [(? symbol? s)
     (cond [(hash-has-key? binaryOps s) (error 'parse "ZNQR: Identifiers cannot be Binary Operaters")]
           [(symbol=? s 'ifleq0) (error 'parse "ZNQR: if-then-else takes exactly 3 args")]
           [(symbol=? s 'func) (error 'parse "ZNQR: can't define functions inside expressions")]
           [else (IdC s)])]
    [(? real? n) (NumC n)]
    [else (error 'parse "ZNQR: invalid input for parse")]))

;Parses a function definition
(: parse-fundef (-> Sexp FunDefC))
(define (parse-fundef s)
  (match s
    [(list 'func rst ...)
     (define len (length rst))
     (cond [(not (= len 2)) (error 'parse-fundef "ZNQR: functions must have a name and a definition/body")])
     (define header (first rst))
     (cond [(not (list? header))
            (error 'parse-fundef "ZNQR: bad syntax- function definitions must have a list its name and args")])
     (cond [(not (symbol? (first (cast header (Listof Any)))))
            (error 'parse-fundef "ZNQR: bad syntax- function name must be given as a symbol")])
     (define name (first (cast header (Listof Any))))
     (define body (second rst))
     (define args (rest (cast header (Listof Any))))
     (cond
       [(not (andmap symbol? args))
        (error 'parse-fundef "ZNQR: bad syntax- args must be given as symbols")])
     (FunDefC (cast name Symbol) (cast args (Listof Symbol)) (parse body))]
    [else (error 'parse-fundef "ZNQR: invalid input for function definition")]))

;Parses a program (a list of function definitions)
(: parse-prog (-> Sexp (Listof FunDefC)))
(define (parse-prog funs)
  (cond [(empty? funs) (error 'parse-prog "ZNQR: invalid program")]
        [else ((inst map FunDefC Sexp) parse-fundef (cast funs (Listof Sexp)))]))

;____________________________________
;Interpreter for "main"

;Interprets the function named main from the fundefs.
(: interp-fns (-> (Listof FunDefC) Real))
(define (interp-fns funs)
  (define mainFunc (first (filter is-main? funs)))
  (interp (FunDefC-body mainFunc) (remove mainFunc funs)))

;Helper function to identify main. Could have been a lambda expression.
(: is-main? (-> FunDefC Boolean))
(define (is-main? fd)
  (equal? (FunDefC-name fd) 'main))

;____________________________________
;Interpreter

;Interprets the given expression, using the list of funs to resolve applications.
(: interp (-> ExprC (Listof FunDefC) Real))
(define (interp exp funs)
  (match exp
    [(NumC n) n]
    [(IdC s) (error 'interp "ZNQR: interp shouldn't get here!")]
    [(BinopC op l r)
     (define opValue
       (hash-ref binaryOps op
                 (lambda () (error 'interp "ZNQR: Given Binary Operation not implemented"))))
     ;check that all arguments, even if unused, are valid
     (define leftVal (interp l funs))
     (define rightVal (interp r funs))
     (cond [(symbol=? op '/) (interp-safe-divide leftVal rightVal)]
           [else (opValue leftVal rightVal)])]
    [(AppC func args) (define fd (get-fundef func funs))
                      ;error if the function application didn't use the same # of args as the def
                      (define params (FunDefC-args fd))
                      (cond [(not (= (length params) (length args)))
                             (error 'interp "ZNQR: Func app must use the same # of args as defined")])
                      ;(Evaluate) check that all arguments (given parameter values), even if unused, are valid
                      ;(Substitute) params->args then Evaluate) finally, interp the function application
                      (interp (interp-subst-AppC (interp-arg-values args funs) params (FunDefC-body fd)) funs)]
    [(ifleq0 i t e) (if (<= (interp i funs) 0) (interp t funs) (interp e funs))]))

;helper function for interp, when dividing, that prevents divide by zero
(: interp-safe-divide (-> Real Real Real))
(define (interp-safe-divide l r)
  (cond [(= r 0) (error 'interp-safe-divide "ZNQR: Can't divide by zero!")]
        [else (/ l r)]))

;helper function for interp, checks that all arguments in a function application, even if unused, are valid
(: interp-arg-values (-> (Listof ExprC) (Listof FunDefC) (Listof ExprC)))
(define (interp-arg-values args funs)
  (cond [(empty? args) '()]
        [else (define arg (first args))
              (cons (NumC (interp arg funs)) (interp-arg-values (rest args) funs))]))

;helper function for interp, definitions of all the functions in our program's scope- from Chapter 5 of PLAI
(: get-fundef (-> Symbol (Listof FunDefC) FunDefC))
(define (get-fundef n fds)
  (cond [(empty? fds)
         (error 'get-fundef "ZNQR: reference to undefined function")]
        [(cons? fds)
         (cond [(equal? n (FunDefC-name (first fds))) (first fds)]
               [else (get-fundef n (rest fds))])]))

;____________________________________
;Substitution

;eager substitution of an argument in our function- from Chapter 5 of PLAI
(: subst (-> ExprC Symbol ExprC ExprC))
(define (subst what for in)
  (match in
    [(NumC n) in]
    [(IdC s) (cond [(symbol=? s for) what]
                   [else in])]
    [(ifleq0 i t e) (ifleq0 (subst what for i) (subst what for t) (subst what for e))]
    [(AppC func args) (AppC func (map (lambda (arg) (subst what for (cast arg ExprC))) args))]
    [(BinopC op l r) (BinopC op (subst what for l)
                             (subst what for r))]))

;helper function for interp that calls subst of each of a function application's args
;in a function body one by one, returning a single ExprC
(: interp-subst-AppC (-> (Listof ExprC) (Listof Symbol) ExprC ExprC))
(define (interp-subst-AppC whats fors in)
  (cond [(empty? whats) in]
        [else (define newIn (subst (first whats) (first fors) in))
              (interp-subst-AppC (rest whats) (rest fors) newIn)]))

;____________________________________
;Overall ZNQR Parser + Interpreter

;Combines parsing and evaluation.
(: top-interp (Sexp -> Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

;________________________________________________________________________
;
;TEST CASES
;________________________________________________________________________
;(OLD / OUT OF DATE TESTS)
;(check-equal? (top-interp '{{func {f x} {+ x 1}} {func {main} {f 5}}}) 6)
;(check-equal? (top-interp '{{func {f x} {-1}} {func {main} {f 5}}}) -1)
;(check-equal? (parse-prog '{func {f x} {-1}}) -1)

;(check-exn (regexp (regexp-quote "ZNQR: invalid input for parse"))
;           (lambda () (top-interp '{{func {main x} {+}}})))
;(check-exn (regexp (regexp-quote "ZNQR: invalid input for function definition"))
;           (lambda () (top-interp '{func {f x}})))
;(check-exn (regexp (regexp-quote "ZNQR: invalid program"))
;           (lambda () (top-interp '{})))

(check-equal? (parse-fundef '{func {f x} 5}) (FunDefC 'f (list 'x) (NumC 5)))
(check-equal? (parse-prog '{{func {f1 x} 5} {func {f2 y} {+ 2 2}}})
              (list (FunDefC 'f1 (list 'x) (NumC 5))
                    (FunDefC 'f2 (list 'y) (BinopC '+ (NumC 2) (NumC 2)))))
(check-equal? (parse '5) (NumC 5))
(check-equal? (top-interp '{{func {main x} {+ 2 2}}}) 4)
(check-equal? (top-interp '{{func {f1 x} 5} {func {main y} {+ 2 2}}}) 4)

;test ifleq0
(check-equal? (parse '{ifleq0 0 {* 3 5} 2})
              (ifleq0 (NumC 0) (BinopC '* (NumC 3) (NumC 5)) (NumC 2)))
(check-equal? (top-interp '{{func {main x} {ifleq0 0 {* 3 5} 2}}}) 15)
(check-equal? (top-interp '{{func {main x} {ifleq0 1 {* 3 5} 2}}}) 2)
(check-equal? (top-interp '{{func {f x} {ifleq0 x x {- x 1}}} {func {main} {f 5}}}) 4)
;test Binop
(check-equal? (parse '{/ 10 2}) (BinopC '/ (NumC 10) (NumC 2)))
(check-equal? (top-interp '{{func {main x} {* 10 2}}}) 20)
;test AppC
(check-equal? (parse-prog '{{func {f x} 5} {func {main y} {f {+ 0 1}}}})
              (list (FunDefC 'f (list 'x) (NumC 5))
                    (FunDefC 'main (list 'y)
                             (AppC 'f (cons (BinopC '+ (NumC 0) (NumC 1)) '()) ))))
(check-equal? (top-interp '{{func {f x} x} {func {main y} {+ {f 2} 1}}}) 3)

;test functions with more or less than 1 arg, including one with 2 args (special case b/c of Binop!)
(check-equal? (parse-prog '{{func {f x y} 5} {func {main} {+ {f 0 0} 1}}})
              (list (FunDefC 'f (list 'x 'y) (NumC 5))
                    (FunDefC 'main '() (BinopC '+ (AppC 'f (list (NumC 0) (NumC 0))) (NumC 1)))))
(check-equal? (top-interp '{{func {f x y} {/ x y}} {func {main} {f 9 3}}}) 3)
(check-equal? (top-interp '{{func {f x y} {/ x y}} {func {main} {- {f 9 3} -10}}}) 13)
(check-equal?
 (top-interp
  '{{func {f x y} {g y x y}} {func {g a b c} {+ {* a b} c}} {func {main} {f 7 2}}}) 16)

;test error catching for parse
(check-exn (regexp (regexp-quote "ZNQR: invalid input for parse"))
           (lambda () (parse '{})))
(check-exn (regexp (regexp-quote "ZNQR: Binary Operations take exactly 2 args"))
           (lambda () (parse '(/ 3 4 5))))
(check-exn (regexp (regexp-quote "ZNQR: Identifiers cannot be Binary Operaters"))
           (lambda () (parse '(+ / 3))))
(check-exn (regexp (regexp-quote "ZNQR: if-then-else takes exactly 3 args"))
           (lambda () (parse 'ifleq0)))
(check-exn (regexp (regexp-quote "ZNQR: if-then-else takes exactly 3 args"))
           (lambda () (parse '{ifleq0 a b})))
(check-exn (regexp (regexp-quote "ZNQR: if-then-else takes exactly 3 args"))
           (lambda () (parse '{ifleq0})))
(check-exn (regexp (regexp-quote "ZNQR: if-then-else takes exactly 3 args"))
           (lambda () (parse '{ifleq0 a b c d})))
(check-exn (regexp (regexp-quote "ZNQR: can't define functions inside expressions"))
           (lambda () (parse 'func)))
(check-exn (regexp (regexp-quote "ZNQR: can't define functions inside expressions"))
           (lambda () (parse '{func a b})))
(check-exn (regexp (regexp-quote "ZNQR: can't define functions inside expressions"))
           (lambda () (parse '{func})))

;test error catching for parse-fundef
(check-exn (regexp (regexp-quote "ZNQR: functions must have a name and a definition/body"))
           (lambda () (parse-fundef '{func {f x}})))
(check-exn (regexp (regexp-quote "ZNQR: bad syntax- function definitions must have a list its name and args"))
           (lambda () (parse-fundef '{func f {x}})))
(check-exn (regexp (regexp-quote "ZNQR: bad syntax- function name must be given as a symbol"))
           (lambda () (parse-fundef '{func {5 x} x})))
(check-exn (regexp (regexp-quote "ZNQR: bad syntax- args must be given as symbols"))
           (lambda () (parse-fundef '{func {f 13} 13})))
(check-exn (regexp (regexp-quote "ZNQR: invalid input for function definition"))
           (lambda () (parse-fundef '{funcc {f x} 13})))

;test error catching for parse-prog
(check-exn (regexp (regexp-quote "ZNQR: invalid program"))
           (lambda () (parse-prog'{})))

;test error catching for interp
(check-exn (regexp (regexp-quote "ZNQR: interp shouldn't get here!"))
           (lambda () (interp (IdC 'q) '())))
(check-exn (regexp (regexp-quote "ZNQR: Given Binary Operation not implemented"))
           (lambda () (interp (BinopC '^ (NumC 5) (NumC 6)) '())))
(check-exn (regexp (regexp-quote "ZNQR: Func app must use the same # of args as defined"))
           (lambda () (top-interp '{{func {f a b} 999} {func {main x} {f x}}})))

;test error catching for interp-safe-divide
(check-exn (regexp (regexp-quote "ZNQR: Can't divide by zero!"))
           (lambda () (top-interp '{{func {f a b} {/ a b}} {func {main} {f 0 0}}})))

;test error catching for get-fundef
(check-exn (regexp (regexp-quote "ZNQR: reference to undefined function"))
           (lambda () (top-interp '{{func {f a b} {+ a b}} {func {main} {f 0 {g 13}}}})))
