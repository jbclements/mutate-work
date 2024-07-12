#lang typed/racket
(require typed/rackunit)

; Implemented full project

; Defines a new language ZODE with as per the spec
(define-type ExprC (U numC ifleq0? binopC idC appC))
(struct numC ([n : Real]) #:transparent)
(struct binopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct ifleq0? ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct idC ([name : Symbol]) #:transparent)
(struct appC ([name : Symbol] [args : (Listof ExprC)]) #:transparent)

; A function definition is not an expression, this defines it
(define-type FunDefC (U fdC))
(struct fdC ([name : Symbol] [arglst : (Listof Symbol)] [body : ExprC]) #:transparent)

; Interperets a binopC operation
(define (interpBinop [op : Symbol] [l : Real] [r : Real]) : Real
     (match op
       ['+
        (+ l r)]
       ['-
        (- l r)]
       ['*
        (* l r)]
       ['/
        (if (equal? r 0) (error 'interpBinop "ZODE Divide by 0") (/ l r))]))

; Searches the function definitions for a specific function, and returns it.
; get-fundef : symbol * (listof FunDefC) -> FunDefC
(define (get-fundef [target : Symbol] [funs : (Listof FunDefC)]) : FunDefC
  (match funs
    [(cons first rest)
     (if
      (symbol=? (fdC-name first) target)
      first
      (get-fundef target rest))]
    ['() (error 'get-fundef "ZODE Undefined function ~e" target)]
    ;[_ (error 'get-fundef "ZODE Invalid function definitions ~e" funs)]
    ))

; Substitues the expression what, for the symbol for, in the expression in
(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  ;(printf "Substituting what : ~s for : ~s in : ~s \n" what for in)
  (match in
    [(idC subject) (if (symbol=? subject for) what in)]
    [(numC n) in]
    [(appC name args)
     (appC name (map (lambda ([arg : ExprC]) (subst what for arg)) args))]
    [(binopC s l r) (binopC s (subst what for l) (subst what for r))]
    [(ifleq0? test then else) (ifleq0? (subst what for test) (subst what for then) (subst what for else))]))

; Substitues multiple params into their variables
(define (subst-multi-param [what : (Listof ExprC)] [for : (Listof Symbol)] [in : ExprC]) : ExprC
  (match what
    [(cons what-first what-rest)
     (match for
         [(cons for-first for-rest)
          (subst-multi-param what-rest for-rest (subst what-first for-first in))]
       ['() (error 'subst-multi-pararm "ZODE Invalid num of params for ~e (too many provided)" for)])]
    ['()
     (match for
         ['() in]
         [_ (error 'subst-multi-param "ZODE Invalid num of params for ~e (too few provided)" for)])]))


; Accepts an ZODE3 expression and "runs" the code, interprets the value
(define (interp [a : ExprC] [fds : (Listof FunDefC)]) : Real
  (match a
    [(numC n) n]
    [(appC name args)
     (define targetfun (get-fundef name fds))
     (interp (subst-multi-param
              (map (lambda ([arg : ExprC]) : ExprC (numC (interp arg fds))) args)
              (fdC-arglst targetfun)
              (fdC-body targetfun)) fds)]
    [(binopC s l r) (interpBinop s (interp l fds) (interp r fds))]   
    [(ifleq0? test then else) (if (<= (interp test fds) 0) (interp then fds) (interp else fds))]
    [(idC val) (error 'interp "ZODE Unbound identifier ~e" val)]))

; Determines if there are duplicate arguments
(define (duplicate-args? [args : (Listof Symbol)]) : Boolean
  (cond
     [(empty? args) #f] 
     [(not (not (member (first args) (rest args)))) #t]
     [else (duplicate-args? (rest args))]))
; Full disclosure, read this StackOverflow page.
; https://stackoverflow.com/questions/9583381/scheme-function-that-checks-a-list-for-duplicates
; I ~think~ I'm allowed to use this, but if not hopefully this transparency limmits the amount
; of credit lost.

; Parses a ZODE format of a function into it's racket structures
(define (parse-fundef [s : Sexp]) : FunDefC
  ;(printf "Expression is ~s" s)
  (match s
    [(list 'def ': (? symbol? name) ': (? symbol? args) ... ': body)
     (if (or
          (symbol=? name '+) (symbol=? name '*) (symbol=? name '-) (symbol=? name '/) (symbol=? name 'ifleq0?)
          (duplicate-args? (cast args (Listof Symbol))))
         (error 'parse-fundef "ZODE Invalid function definition")
         (fdC name (cast args (Listof Symbol)) (parse body)))]
    [_ (error 'parse-fundef "ZODE Invalid function definition")]))


; Parses a ZODE program into the list of racket function structures it represents
(define (parse-prog [s : Sexp]): (Listof FunDefC)
  (match s
    [(cons f r)
     ;(printf "First is ~s\n" f)
     ;(printf "Rest is ~s" r)
     (cons (parse-fundef f) (parse-prog r))]
    ['() '()]))
 
; Accepts an s-expression and parses it into an ArithC expression
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? symbol? arg)
     (if (or (symbol=? arg '+) (symbol=? arg '*)
             (symbol=? arg '-) (symbol=? arg '/)
             (symbol=? arg 'ifleq0?) (symbol=? arg 'def))
         (error 'parse "ZODE Can't use keyword as variable") (idC arg))
     ]
    [(list '+ l r) (binopC '+ (parse l) (parse r))]
    [(list '* l r) (binopC '* (parse l) (parse r))]
    [(list '- l r) (binopC '- (parse l) (parse r))]
    [(list '/ l r) (binopC '/ (parse l) (parse r))]
    [(list 'ifleq0? ': test ': then ': else) (ifleq0? (parse test) (parse then) (parse else))]
    [(list (? symbol? name) args ...)
     (if (or (symbol=? name '+) (symbol=? name '*) (symbol=? name '-) (symbol=? name '/) (symbol=? name 'ifleq0?))
         (error 'parse "ZODE Invalid num of args for ~s" name) (appC name (map parse args)))
     ]
    [(? real? n) (numC n)]))


; Accepts an s-expression in the ZODE language and evaluates it
(define (top-interp [s : Sexp]) : Number
  (define fds (parse-prog s))
  ;(define mainfunc (get-fundef 'main fds))
  (interp (appC 'main '()) fds))

; Get-fundef Tests
(check-equal? (get-fundef 'myfun
                          (list
                           (fdC 'notmyfun '(x) (binopC '+ (numC 1) (numC 1)))
                           (fdC 'myfun '(x) (binopC '+ (numC 1) (numC 1)))))
              (fdC 'myfun '(x) (binopC '+ (numC 1) (numC 1))))
(check-exn (regexp (regexp-quote "ZODE Undefined function")) (lambda () (get-fundef 'unkown '())))
; Subst Tests
(check-equal?
 (subst
  (binopC '+ (numC 1) (numC 2)) 'x (binopC '* (idC 'x) (idC 'x)))
 (binopC '* (binopC '+ (numC 1) (numC 2)) (binopC '+ (numC 1) (numC 2))))
; Interp Tests
(check-equal? (interp (binopC '+ (numC 3) (numC 5)) '()) 8)
(check-equal? (interp (binopC '* (numC 3) (numC 5)) '()) 15)
(check-equal? (interp (binopC '+ (binopC '* (numC 2) (numC 4)) (numC 5)) '()) 13)
(check-equal? (interp (ifleq0? (numC 4) (binopC '+ (numC 4) (numC 4)) (binopC '+ (numC 4) (numC 1))) '()) 5)
(check-equal? (interp (ifleq0? (numC -4) (binopC '+ (numC 4) (numC 4)) (binopC '+ (numC 4) (numC 1))) '()) 8)
(check-equal? (interp (binopC '+ (numC 3) (appC 'myfun (list (numC 3))))
                      (list (fdC 'myfun '(x) (binopC '+ (idC 'x) (idC 'x))))) 9)
(check-exn (regexp (regexp-quote "ZODE Unbound identifier")) (lambda () (interp (binopC '+ (numC 4) (idC 'x)) '())))
(check-equal? (interp
               (appC 'myfun (list (numC 3) (numC  4)))
               (list (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y))))) 7)
(check-equal? (interp
               (appC 'myfun (list (numC 1) (numC 2)))
               (list (fdC 'myfun '(x y) (ifleq0? (binopC '+ (idC 'x) (idC 'y)) (numC 1) (numC 0))))) 0)
(check-equal? (interp
               (appC 'myfun (list (numC -1) (numC -2)))
               (list (fdC 'myfun '(x y) (ifleq0? (binopC '+ (idC 'x) (idC 'y)) (numC 1) (numC 0))))) 1)
(check-equal? (interp
              (appC 'myfun (list (numC 3) (appC 'mysecfun (list (numC 1) (numC 2)))))
              (list
               (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y)))
               (fdC 'mysecfun '(t n) (binopC '* (idC 't) (idC 'n))))) 5)
(check-equal? (interp
              (appC 'myfun (list (numC 3) (appC 'mysecfun (list (numC 1) (numC 2)))))
              (list
               (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y)))
               (fdC 'mysecfun '(t n) (binopC '* (appC 'myfun (list (idC 't) (idC 't))) (idC 'n))))) 7)
(check-exn (regexp (regexp-quote "ZODE Invalid num of params")) (lambda () (interp
               (appC 'myfun '())
               (list (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y)))))))
(check-exn (regexp (regexp-quote "ZODE Invalid num of params")) (lambda () (interp
               (appC 'myfun (list (numC 1) (numC 2) (numC 3)))
               (list (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y)))))))
(check-equal? (interp
               (appC 'main '())
               (list (fdC 'main '() (binopC '+ (numC 1) (numC 2))))) 3)
; Parse fun def Tests
(check-equal? (parse-fundef '{def : myfun : x y : {+ x y}}) (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y))))
(check-exn (regexp (regexp-quote "ZODE Invalid function definition"))
           (lambda () (parse-fundef '{def : + : : 13})))
(check-exn (regexp (regexp-quote "ZODE Invalid function definition"))
           (lambda () (parse-fundef '{def : g : : 13 42})))
(check-exn (regexp (regexp-quote "ZODE Invalid function definition"))
           (lambda () (parse-fundef '{def : g : z z : 13})))
; parse prog tests
(check-equal? (parse-prog
               '{
                 {def : myfun : x y : {+ x y}}
                 {def : main : : {myfun 1 2}}
                 })
              (list
               (fdC 'myfun '(x y) (binopC '+ (idC 'x) (idC 'y)))
              (fdC 'main '() (appC 'myfun (list (numC 1) (numC 2))))))
; Parser Tests
(check-equal? (parse '{+ 1 2}) (binopC '+ (numC 1) (numC 2)))
(check-equal? (parse 1) (numC 1))
(check-equal? (parse '{* 1 2}) (binopC '* (numC 1) (numC 2)))
(check-equal? (parse '{+ {* 3 4} 2}) (binopC '+ (binopC '* (numC 3) (numC 4)) (numC 2)))
(check-equal? (parse '{ifleq0? : {* 3 4} : {+ 1 2} : {+ 3 4}})
              (ifleq0? (binopC '* (numC 3) (numC 4)) (binopC '+ (numC 1) (numC 2)) (binopC '+ (numC 3) (numC 4))))
(check-equal? (parse '{myfun 1 2}) (appC 'myfun (list (numC 1) (numC 2))))
(check-exn (regexp (regexp-quote "ZODE Invalid num of args for +")) (lambda () (parse '{+ 1 2 3})))
(check-exn (regexp (regexp-quote "ZODE Invalid num of args for -")) (lambda () (parse '{- 1 2 3})))
(check-exn (regexp (regexp-quote "ZODE Invalid num of args for *")) (lambda () (parse '{* 1 2 3})))
(check-exn (regexp (regexp-quote "ZODE Invalid num of args for /")) (lambda () (parse '{/ 1 2 3})))
(check-exn (regexp (regexp-quote "ZODE Invalid num of args for ifleq0?")) (lambda () (parse '{ifleq0? 1 2 3 4})))
(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse '{+ + 2})))
(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse '{- - 2 })))
(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse '{* * 2 })))
(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse '{/ / 2 })))
(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse 'ifleq0?)))
(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse '{+ def a})))
;(check-exn (regexp (regexp-quote "ZODE Can't use keyword as variable")) (lambda () (parse '{ifleq0? ifleq0? 2 3})))
; Top Interp Tests
(check-equal? (top-interp
               '{{def : main : : {myfun 1 2}}
                 {def : myfun : x y : {+ x y}}})
              3)

(check-equal? (top-interp
               '{{def : main : : {myfun 1 2}}
                 {def : myfun : x y : {- 1 {+ x y}}}})
              -2)
(check-equal? (top-interp
               '{{def : main : : {myfun 1 2}}
                 {def : myfun : x y : {/ 3 {+ x y}}}})
              1)
(check-exn (regexp (regexp-quote "ZODE Divide by 0"))
           (lambda () (top-interp '{{def : ignoreit : x : {+ 3 4}} {def : main : : {ignoreit {/ 1 {+ 0 0}}}}})))