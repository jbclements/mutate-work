#lang typed/racket
(require typed/rackunit)


;; Defining data types for the program.
(define-type ExprC (U NumC BinOpC leq0? IdC AppC))
(struct NumC ([n : Real]) #:transparent)
(struct BinOpC ([s : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct leq0? ([cond : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct FundefC ([name : Symbol] [arg : Symbol] [body : ExprC]) #:transparent)
(struct IdC  ([s : Symbol]) #:transparent)
(struct AppC ([fun : Symbol] [arg : ExprC]) #:transparent)


;; reserved() accepts a symbol and check if the symbol is reserved for the language.
(define (reserved [s : Symbol]) : Boolean
  (match s
    ['+ #t]
    ['- #t]
    ['/ #t]
    ['* #t]
    ['leq0? #t]
    ['then #t]
    ['else #t]
    ['= #t]
    ['def #t]
    [other #f]))


;; binary returns true if it is a binary operation.
(define (binary [s : Symbol]) : Boolean
  (match s
    ['+ #t]
    ['- #t]
    ['/ #t]
    ['* #t]
    [other #f]))


;; parse s takes sexp and translate it to ExprC.
(define (parse [s : Sexp]) : ExprC
  (match s
    ;; if real num
    [(? real? a) (NumC a)]
    ;; if symbol
    [(? symbol? a) (if (reserved a)
                       (error 'parse "VVQS3 - invalid argument for operation")
                       (IdC a))]
    ;; if a function with exactly one var
    [(list (? symbol? a) b) (if (reserved a)
                                (error 'parse "VVQS3 - invalid args")
                                (AppC a (parse b)))]
    ;; body of function
    [(list (? symbol? a) b c)
     (if (binary a) (BinOpC a (parse b) (parse c))
         (error 'parse "VVQS3 - list of three things cannot be parsed"))]
    ;; leq0? implementation
    [(list 'leq0? a 'then b 'else c) (leq0? (parse a) (parse b) (parse c))]
    ;; otherwise error
    [other (error 'parse "VVQS3 - no match pattern found")]))


;; parse-fundef parses a Sexp function and return a FundefC
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    [(list 'def (list 'main 'init) '= (? list? l)) (FundefC 'main 'init (parse l))]
    [(list 'def (list (? symbol? a) (? symbol? b)) '= c)
     (if (and (not (reserved a)) (not (reserved b)))
         (FundefC a b (parse c))
         (error 'parse-fundef
                "Invalid function declaration in VVQS3: ~e" s))] 
    [other (error 'parse-fundef "Invalid function declaration in VVQS3: ~e" s)]))


;; parse-prog takes list of Sexp functions and
;; return a list of function definitions.
(define (parse-prog [s : Sexp]) : (Listof FundefC)
  (match s
    [(cons f r) (cons (parse-fundef f) (parse-prog r))]
    ['() '()]
    [other (error 'parse-prog "VVQS3: Invalid argument ~e" s)]))


;; matches an expression to list of functions, along the way
;; also substitutes variables from arguments to be evaluated.
(define (interp [exp : ExprC] [fds : (Listof FundefC)]) : Real
  (match exp
    [(NumC n) n]
    [(BinOpC '+ l r) (+ (interp l fds) (interp r fds))]
    [(BinOpC '- l r) (- (interp l fds) (interp r fds))]
    [(BinOpC '* l r) (* (interp l fds) (interp r fds))]
    [(BinOpC '/ l r) (/ (interp l fds) (if (equal? (interp r fds) 0)
                                           (error 'interp "VVQS3 - shouldn't get here")
                                           (interp r fds)))]
    [(leq0? test then els) (if (<= (interp test fds) 0)
                               (interp then fds)
                               (interp els fds))]
    [(AppC f a) (define fd (get-fundef f fds))
                (interp a fds)
                (interp (subst a (FundefC-arg fd) (FundefC-body fd))
                        fds)]
    [(IdC _) (error 'interp "VVQS3 - shouldn't get here")]))


;; get-fundef returns a particular function definition from list of functions.
(define (get-fundef [n : Symbol] [fds : (Listof FundefC)]) : FundefC
  (cond
    [(empty? fds) (error 'get-fundef "VVQS3 - reference to undefined function")]
    [(cons? fds) (cond
                   [(equal? n (FundefC-name (first fds))) (first fds)]
                   [else (get-fundef n (rest fds))])]))


;; subst will substitute a function body with a real integer on an argument.
(define (subst [sub : ExprC] [arg : Symbol] [body : ExprC]) : ExprC
  (match body
    [(NumC n) body]
    [(IdC s) (if (eq? s arg) sub body)]
    [(AppC f a) (AppC f (subst sub arg a))]
    [(BinOpC s l r) (BinOpC s (subst sub arg l) (subst sub arg r))]
    [(leq0? test then els) (leq0? (subst sub arg test)
                                  (subst sub arg then)
                                  (subst sub arg els))]))


;; interp-fns will look for the main function and will evaluate main based on
;; the list of functions defined.
(define (interp-fns [fns : (Listof FundefC)]) : Real 
   (interp (AppC 'main (NumC 0)) fns))


;; top-interp is a shortcut of passing Sexp of function lists and evaluating main,
;; resulting a real final number.
(define (top-interp [fun-sexps : Sexp]) : Real
  (interp-fns (parse-prog fun-sexps)))


;; ALL TEST CASES
(define f '(def (f x) = (+ x 14)))
(define main '(def (main init) = (f 2)))
(define funs '{{def {f x} = {+ x 14}} {def {main init} = {f 2}}})
(define bigFunction '{{def {f x} = {- x 2}}
                      {def {g y} = {* y 3}}
                      {def {h z} = {+ z 5}}
                      {def {i a} = {/ a 4}}
                      {def {main init} = {g {f {h {i {+ 4 {* 4 6}}}}}}}})
(define testEq '{{def {j x} = {leq0? x
                                          then x
                                          else {- x 1}}}
                 {def {main init} = {j 2}}})
(define fxn '{{def {f x} = {+ {g x} 3}}
              {def {g y} = {- 3 y}}
              {def {main init} = {f 2}}})
(define fxn2 '{{def {f x} = {+ {g x} 3}}
              {def {g y} = {- 3 y}}
              {def {main init} = {h 2}}})
(define fxn3'{{def {f x} = {leq0? x then x else {- x 1}}}
              {def {main init} = {f 0}}})
(define fxn4'{{def {f x} = {leq0? x then x else {- x 1}}}
              {def {main init} = {f 1}}})
(define fxn5'{{def {f x} = {leq0? x then x else {* x 5}}}
              {def {main init} = {f 5}}})
(check-equal? (top-interp fxn3) 0)
(check-equal? (top-interp fxn4) 0)
(check-equal? (top-interp fxn5) 25)
(check-equal? (list (FundefC 'f 'x (BinOpC '+ (IdC 'x) (NumC 14)))
                    (FundefC 'main 'init (AppC 'f (NumC 2))))
              (parse-prog (list f main)))
(check-equal? (parse 5) (NumC 5))
(check-equal? (reserved '+) #t)
(check-equal? (reserved '-) #t)
(check-equal? (reserved '/) #t)
(check-equal? (reserved '*) #t)
(check-equal? (reserved 'ab) #f)
(check-equal? (parse '(+ (- 2 1) 2)) (BinOpC '+ (BinOpC '- (NumC 2)
                                                        (NumC 1)) (NumC 2)))
(check-equal? (parse '(* 1 2)) (BinOpC '* (NumC 1) (NumC 2)))
(check-equal? (parse '{leq0? x then x else {- x 1}})
              (leq0? (IdC 'x) (IdC 'x) (BinOpC '- (IdC 'x) (NumC 1))))
(check-equal? (FundefC 'f 'x (BinOpC '+ (IdC 'x) (NumC 14))) (parse-fundef f))
(check-equal? (FundefC 'main 'init (AppC 'f (NumC 2))) (parse-fundef main))
(check-equal? (parse-fundef '{def {h x} = {* 5 x}})
              (FundefC 'h 'x
                       (BinOpC '* (NumC 5) (IdC 'x))))
(check-equal? (interp-fns
               (parse-prog '{{def {f x} = {+ x 14}}
                             {def {main init} = {f 2}}}))
              16)
(check-equal? (parse '{leq0? x then x else {- x 1}})
              (leq0? (IdC 'x) (IdC 'x) (BinOpC '- (IdC 'x) (NumC 1))))
(check-equal? 16 (interp (AppC 'f (NumC 2)) (parse-prog funs)))
(check-equal? (top-interp bigFunction) 30)
(check-equal? (top-interp fxn) 4)
(check-equal? (subst (IdC 'abc) 'x (IdC 'bcd)) (IdC 'bcd))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse-fundef '+)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '(& 1 2))))
(check-equal? (parse 'abcd) (IdC 'abcd))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '+)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse 'leq0?)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse 'then)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse 'else)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '=)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse-prog f)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse-prog 'f)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '(1 + 2))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '(1 + -))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '(* + /))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '(leq0? 1))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (interp (IdC 's) (parse-prog funs))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (interp (AppC 'g (NumC 1)) (parse-prog funs))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (top-interp fxn2)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (interp (IdC 'ahnkgjasd) (parse-prog fxn2))))
(define firstTest '{{def {minus-five x} = {+ x {* -1 5}}}
                    {def {main init} = {minus-five {+ 8 init}}}})
(check-equal? (top-interp firstTest) 3)
(check-equal? (parse-fundef '(def (f x) = 6)) (FundefC 'f 'x (NumC 6)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse-fundef '(def (+ x) = 13))))

(define fun '((def (ignoreit x) = (+ 3 4))
              (def (main init) = (ignoreit (/ 1 (+ 0 0))))))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (top-interp fun)))
(check-exn (regexp (regexp-quote "VVQS3"))
           (lambda () (parse '(+ def a))))
(define b '(def (f x) = (= 1)))