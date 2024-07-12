#lang typed/racket

(require typed/rackunit)

(define-syntax tstruct
    (syntax-rules ()
      [(_ name fields)
       (struct name fields #:transparent)]))

  (provide tstruct)

(define-type ExprC (U NumC PlusC MultC IdC AppC IfLeq0C))
  (tstruct NumC ([n : Real]))
  (tstruct PlusC ([l : ExprC] [r : ExprC]))
  (tstruct MultC ([l : ExprC] [r : ExprC]))
  (tstruct IdC ([s : Symbol]))
  (tstruct AppC ([fun : Symbol] [arg : ExprC]))
  (tstruct IfLeq0C ([test : ExprC] [then : ExprC] [else : ExprC]))

(tstruct FunDefC ([name : Symbol] [arg : Symbol] [body : ExprC]))

;top-level interpreter that evaluates s-expressions
(define (top-interp [fun-sexps : (Listof Sexp)]) : Real
  (interp-fns (parse-prog fun-sexps)))

;Interprets the function named main from the fundefs
(define (interp-fns [funs : (Listof FunDefC)]) : Real
  ;need to check if main is defined twice somewhere else
  (define mainFuncCheck (findf (lambda ([fun : FunDefC]) (eq? 'main (FunDefC-name fun))) funs))
  (if mainFuncCheck (interp (FunDefC-body mainFuncCheck) funs) (error 'ZNQR "no main method found"))
  )

;parses program into list of function definitions (FundefC)
(define (parse-prog [fun-sexps : (Listof Sexp)]) : (Listof FunDefC)
  (if (eq? (length fun-sexps) 0) '()
    (match (first fun-sexps)
    [(list 'func name arg body) (cons (parse-fundef (first fun-sexps)) (parse-prog (rest fun-sexps)))]
    [(list 'func name body) (cons (parse-fundef (first fun-sexps)) (parse-prog (rest fun-sexps)))]
    [else (error 'ZNQR "invalid program syntax, is something not in a function?")])
    )
  )

;parses an s-expression into fundef
(define (parse-fundef [s : Sexp]) : FunDefC
  (match s
    [(list 'func (list (? symbol? name) (? symbol? arg)) body) (FunDefC name arg (parse body))]
    [(list 'func (list (? symbol? name)) body) (FunDefC name 'NULL (parse body))]
    [else (error 'ZNQR "failed to parse function")]))


;interprets result of function calls
(define (interp [e : ExprC] [fds : (Listof FunDefC)]) : Real
  (match e
      [(NumC n) n]
      [(IdC _) (error 'ZNQR "shouldn't get here")]
      [(AppC f a) (define fd (get-fundef f fds))
                (interp (subst a
                               (FunDefC-arg fd)
                               (FunDefC-body fd))
                        fds)]
      [(PlusC l r) (+ (interp l fds) (interp r fds))]
      [(MultC l r) (* (interp l fds) (interp r fds))]
      [(IfLeq0C ts th el) (if (<= (interp ts fds) 0) (interp th fds) (interp el fds))])
  )

;parser taking s-exp and turning it into ArithS
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    [(? symbol? s) (IdC s)]
    [(list '+ l r) (PlusC (parse l) (parse r))]
    [(list '* l r) (MultC (parse l) (parse r))]
    [(list (? symbol? fun) arg) (AppC fun (parse arg))]
    [(list 'ifleq0 ts th el) (IfLeq0C (parse ts) (parse th) (parse el))]
    [else (error 'ZNQR "invalid input")]))

;finds specific fundef within list of fundefs
(define (get-fundef [n : Symbol] [fds : (Listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds)
     (error 'ZNQR "reference to undefined function")]
    [(cons? fds)
     (cond
       [(equal? n (FunDefC-name (first fds))) (first fds)]
       [else (get-fundef n (rest fds))])]))

;substitutes variables for values in functions
(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
    (match in
    [(NumC n) in]
    [(IdC s) (cond
               [(symbol=? s for) what]
               [else in])]
    [(AppC f a) (AppC f (subst what for a))]
    [(PlusC l r) (PlusC (subst what for l)
                        (subst what for r))]
    [(MultC l r) (MultC (subst what for l)
                        (subst what for r))]
    [(IfLeq0C ts th el) (IfLeq0C (subst what for ts)
                                 (subst what for th)
                                 (subst what for el))])

    )

;---------Tests----------
(check-equal? (parse-prog '{{func {f x} {+ x 1}}{func {main} {f 1}}})
      (list (FunDefC 'f 'x (PlusC (IdC 'x) (NumC 1))) (FunDefC 'main 'NULL (AppC 'f (NumC 1)))))

(check-equal? (parse '(+ 2 3)) (PlusC (NumC 2) (NumC 3)))
(check-equal? (parse '(* 2 3)) (MultC (NumC 2) (NumC 3)))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '(f (+ 2 4))) (AppC 'f (PlusC (NumC 2) (NumC 4))))
(check-equal? (parse '{f {ifleq0 1
     1
     {+ 1 1}}}) (AppC 'f (IfLeq0C (NumC 1) (NumC 1) (PlusC (NumC 1) (NumC 1)))))

(check-equal? (parse-fundef '{func {f x} {+ x 1}}) (FunDefC 'f 'x (PlusC (IdC 'x) (NumC 1))))

(check-equal? (interp (AppC 'f (PlusC (NumC 2) (NumC 4))) (list (FunDefC 'f 'x (PlusC (IdC 'x) (NumC 1))))) 7)

(check-equal? (subst (NumC 1) 'x (PlusC (NumC 1) (IdC 'x))) (PlusC (NumC 1) (NumC 1)))

(check-equal? (get-fundef 'f (list (FunDefC 'f 'x
               (PlusC (IdC 'x) (NumC 1))))) (FunDefC 'f 'x (PlusC (IdC 'x) (NumC 1))))

(check-equal? (top-interp '{{func {f x} {ifleq0 x
     x
     {+ x 1}}}{func {main} {f 1}}}) 2)

(check-equal? (top-interp '{{func {f x} {+ x 1}}{func {main} {f 1}}})
      2)



