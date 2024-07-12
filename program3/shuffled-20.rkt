#lang typed/racket


(require typed/rackunit)

;;> eyeball: 5/6, generally good, see comments below.

;;> looks like a parse error. Oog, it was 'equal?'. You have no tests of parsing
;;> that use 'equal?'.

;;> missing strings?

; I implemented everything and got it working the best I could but it fails the last 3 testcases.
; I could not gleam enough information to determine why. I made a post to piazza and got a suggestion
; but it does not appear to solve the issue in testcase 3. Do you have any suggestions? Thanks.



#|--- Definitions/Structs Below ---|#



; Define what an ExprC can be
(define-type ExprC (U numC ifC IdC AppC lamC))
(struct numC ([n : Real]) #:transparent)
(struct ifC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)


; Definition of Bindings, used for constructing the environment
(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof Binding))


; Define what Value can be
(define-type Value (U numV BooleanV closV String PrimV))
(struct numV ([n : Real]) #:transparent)
(struct BooleanV ([bool : Boolean]) #:transparent)
(struct closV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([oper : Symbol]) #:transparent)


;;> ooh, equal? shouldn't be in this list. you have no tests of equal?
; Keyword list, cannot be IdC symbols
(define key-lst '(equal? if var = ->))


; Top environment list, standard bindings passed into top-interp
(define top-env (list (Binding 'true (BooleanV #t)) (Binding 'false (BooleanV #f)) (Binding '+ (PrimV '+))
                      (Binding '- (PrimV '-)) (Binding '* (PrimV '*)) (Binding '/ (PrimV '/))
                      (Binding '<= (PrimV '<=)) (Binding 'equal? (PrimV 'equal?))))




#|--- Functions Below ---|#




;; consumes an s-expression and calls the parser and then the interp function with the top-level environment
(: top-interp (-> Sexp String))
(define (top-interp sexp)
  (serialize (interp (parse sexp) top-env)))


;; consumes an ExprC and Listof FundefC and returns a real
;; Interprets based on input of exp
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(numC n) (numV n)]
    [(IdC x) (lookup x env)]
    ;;> this double-interp will lead to exponential behavior on certain programs:
    [(ifC test then else) (if (BooleanV? (interp test env))
                              (if (BooleanV-bool (cast (interp test env) BooleanV))
                                  (interp then env)
                                  (interp else env))
                              (error 'interp "ZNQR: test expression does not produce boolean"))]
    [(lamC params body) (closV params body env)]
    [(AppC fun args) (match (interp fun env)
                       [(PrimV op) (if (= (length args) 2)
                                       (prim-handler op (interp (first args) env) (interp (second args) env))
                                       (error 'interp "ZNQR: too many operator args"))]
                       [(closV clos-params body clos-env) (if (= (length args) (length clos-params))
                                                              (interp body
                                                                      (append (for/list : (Listof Binding)
                                                                                ([param clos-params] [arg args])
                                                                                (Binding param (interp arg env)))
                                                                              clos-env))
                                                              (error 'interp "ZNQR: mismatching args and params"))]
                       [else (error 'interp "ZNQR: incorrect match in AppC")])]))


;; Consumes Sexp and produces an ExprC
;; Parses sexp and creates data types we can work with.
(define (parse [sexp : Sexp]) : ExprC
  (match sexp
    [(? real? num) (numC num)]
    [(list 'if test then else) (ifC (parse test) (parse then) (parse else))]
    [(? symbol? sym) (if (list-contains sym key-lst)
                         (error 'parse "ZNQR: reserved word ~e used in IdC"
                                sym)
                         (IdC sym))]
    [(list (list (? symbol? syms) ...) '-> body) (if (dup-check (cast syms (Listof Symbol)))
                                                     (error 'parse "ZNQR: duplicate parameter names")
                                                     (lamC (cast syms (Listof Symbol)) (parse body)))]
    [(list 'var (list (? symbol? syms) '= exprs) ... body) (if (dup-check (cast syms (Listof Symbol)))
                                                               (error 'parse "ZNQR: duplicate parameter names")
                                                               (AppC (lamC (cast syms (Listof Symbol)) (parse body))
                                                                     (map parse (cast exprs (Listof Sexp)))))]
    [(list exp ...) (AppC (parse (first exp)) (map parse (rest exp)))]))


;; consumes a symbol and two Values returns a Value
;; returned value will be a numV or BooleanV
(define (prim-handler [oper : Symbol] [val1 : Value] [val2 : Value]) : Value
  (if (list-contains oper '(+ - * / <=))
      (cond
        [(and (numV? val1) (numV? val2)) (cond
                                           [(equal? oper '+) (numV (+ (numV-n val1) (numV-n val2)))]
                                           [(equal? oper '-) (numV (- (numV-n val1) (numV-n val2)))]
                                           [(equal? oper '*) (numV (* (numV-n val1) (numV-n val2)))]
                                           [(equal? oper '/) (if (= (numV-n val2) 0)
                                                                 (error 'prim-handler "ZNQR: division by 0")
                                                                 (numV (/ (numV-n val1) (numV-n val2))))]
                                           [else (BooleanV (<= (numV-n val1) (numV-n val2)))])]
        [else (error 'prim-handler "ZNQR: one argument was not a number")])
      (if (equal? oper 'equal?)
          (cond
            [(and (numV? val1) (numV? val2)) (BooleanV (= (numV-n val1) (numV-n val2)))]
            [(and (BooleanV? val1) (BooleanV? val2)) (BooleanV (and (BooleanV-bool val1) (BooleanV-bool val2)))]
            [(and (string? val1) (string? val2)) (BooleanV (equal? val1 val2))]
            [else (BooleanV #f)])
          (error 'prim-handler "ZNQR: unrecognized operator"))))


;; consumes a ZNQR3 value, and returns a string representation of the value
(define (serialize [val : Value]) : String
  (match val
    [(? numV? n) (~v (numV-n n))]
    [(? string? str) str]
    [(? BooleanV? bool) (if (BooleanV-bool bool)
                            "true"
                            "false")]
    [(closV args body env) "#<procedure>"]
    [(PrimV sym) (symbol->string sym)]))


;; consumes a symbol and environment
;; returns the value associated with that binding
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "ZNQR: name not found ~e" for)]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (Binding-val (first env))]
            [else (lookup for (rest env))])]))


;; consumes a symbol and a Listof Symbol
;; returns a boolean, true if that symbol is in the list
(define (list-contains [sym : Symbol] [lst : (Listof Symbol)]) : Boolean
  (cond
    [(empty? lst) #f]
    [else (if (equal? sym (first lst))
              #t
              (list-contains sym (rest lst)))]))


;; consumes a list and returns a boolean
;; true if there is a duplciate in the list
(define (dup-check [lst : (Listof Symbol)]) : Boolean
  (cond
    [(empty? lst) #f]
    [else (if (list-contains (first lst) (rest lst))
              #t
              (dup-check (rest lst)))]))



#|--- Testcases ---|#



; top-interp testcases
(check-equal? (top-interp '{{{f g} -> {+ {f 2} {g 9}}} {{x} -> {+ x 1}} {{z} -> {+ z 2}}}) "14")
(check-exn (regexp (regexp-quote " ZNQR: incorrect match in AppC"))
           (lambda () (top-interp `(3 4 5))))

; interp testcases
(check-equal? (interp (parse '{{{f g} -> {+ {f 2} {g 9}}} {{x} -> {+ x 1}} {{z} -> {+ z 2}}}) top-env) (numV 14))
(check-exn (regexp (regexp-quote "ZNQR: too many operator args"))
           (lambda () (interp (parse '{{{f g} -> {+ {f 2} {g 9}}} {{x} -> {+ x 1 3}} {{z} -> {+ z 2}}}) top-env)))
(check-exn (regexp (regexp-quote "ZNQR: mismatching args and params"))
           (lambda () (interp (parse '{{{f g} -> {+ {f 2} {g 9}}} {{x} -> {+ x 1 3}} {{z} -> {+ z 2}} {3}}) top-env)))
(check-equal? (interp (ifC (AppC (IdC '<=) (list (numC 3) (numC 2))) (numC 2) (numC 3)) top-env) (numV 3))
(check-equal? (interp (ifC (AppC (IdC '<=) (list (numC 2) (numC 2))) (numC 2) (numC 3)) top-env) (numV 2))
(check-exn (regexp (regexp-quote "ZNQR: test expression does not produce boolean"))
           (lambda () (interp (ifC (numC 2) (numC 2) (numC 3)) top-env)))

; parse testcases
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}}) (AppC (lamC '(z y) (AppC (IdC '+)
                                                                                      (list (IdC 'z) (IdC 'y))))
                                                                   (list (AppC (IdC '+)
                                                                               (list (numC 9) (numC 14))) (numC 98))))
(check-equal? (parse '{var 3}) (AppC (lamC '() (numC 3)) '()))
(check-exn (regexp (regexp-quote "ZNQR: reserved word used in IdC"))
           (lambda () (parse 'var)))
(check-exn (regexp (regexp-quote "ZNQR: duplicate parameter names"))
           (lambda () (parse '{{x x} -> {x}})))
(check-equal? (parse '{{{f g} -> {+ {f 2} {g 9}}} {{x} -> {+ x 1}} {{z} -> {+ z 2}}})
              (AppC
               (lamC '(f g) (AppC (IdC '+) (list (AppC (IdC 'f) (list (numC 2))) (AppC (IdC 'g) (list (numC 9))))))
               (list (lamC '(x) (AppC (IdC '+) (list (IdC 'x) (numC 1))))
                     (lamC '(z) (AppC (IdC '+) (list (IdC 'z) (numC 2)))))))
(check-exn (regexp (regexp-quote "ZNQR: duplicate parameter names"))
           (lambda () (parse '{var {z = {+ 9 14}} {z = 98} {+ z y}})))
(check-equal? (parse '(if (<= 3 2) 2 3)) (ifC (AppC (IdC '<=) (list (numC 3) (numC 2))) (numC 2) (numC 3)))

; prim-handler testcases
(check-equal? (prim-handler '- (numV 2) (numV 2)) (numV 0))
(check-equal? (prim-handler '* (numV 2) (numV 2)) (numV 4))
(check-equal? (prim-handler '/ (numV 2) (numV 2)) (numV 1))
(check-exn (regexp (regexp-quote "ZNQR: division by 0"))
           (lambda () (prim-handler '/ (numV 2) (numV 0))))
(check-equal? (prim-handler '<= (numV 2) (numV 2)) (BooleanV #t))
(check-exn (regexp (regexp-quote "ZNQR: one argument was not a number"))
           (lambda () (prim-handler '/ (numV 2) (BooleanV #t))))
(check-equal? (prim-handler 'equal? (numV 2) (numV 2)) (BooleanV #t))
(check-equal? (prim-handler 'equal? (BooleanV #t) (BooleanV #f)) (BooleanV #f))
(check-equal? (prim-handler 'equal? "works" "words") (BooleanV #f))
(check-equal? (prim-handler 'equal? "works" (numV 2)) (BooleanV #f))
(check-exn (regexp (regexp-quote "ZNQR: unrecognized operator"))
           (lambda () (prim-handler 'fail (numV 2) (BooleanV #t))))

; serialize testcases
(check-equal? (serialize (numV 8)) "8")
(check-equal? (serialize (BooleanV #t)) "true")
(check-equal? (serialize (BooleanV #f)) "false")
(check-equal? (serialize (closV '() (numC 1) top-env)) "#<procedure>")
(check-equal? (serialize (PrimV '+)) "+")
(check-equal? (serialize "word") "word")

; lookup testcases
(check-equal? (lookup '+ top-env) (PrimV '+))
(check-exn (regexp (regexp-quote "ZNQR: name not found"))
           (lambda () (lookup 'fail top-env)))

; list-contains testcases
(check-equal? (list-contains 'a '()) #f)
(check-equal? (list-contains 's '(a b d c)) #f)
(check-equal? (list-contains 'c '(a b s d c)) #t)

; dup-check testcases
(check-equal? (dup-check '()) #f)
(check-equal? (dup-check '(a b b c d)) #t)

 (parse (quote (((empty) -> (((cons) -> (((empty?) -> (((first) -> (((rest) -> (((Y) -> (((length) -> (((addup) -> (addup (cons 3 (cons 17 empty)))) (Y ((addup) -> ((l) -> (if (empty? l) 0 (+ (first l) (addup (rest l))))))))) (Y ((length) -> ((l) -> (if (empty? l) 0 (+ 1 (length (rest l))))))))) (((x) -> ((y) -> (y ((z) -> (((x x) y) z))))) ((x) -> ((y) -> (y ((z) -> (((x x) y) z)))))))) ((l) -> (l false)))) ((l) -> (l true)))) ((l) -> (equal? l empty)))) ((a b) -> ((select) -> (if select a b))))) 13)))
