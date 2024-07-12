#lang typed/racket

;;> eyeball: 4/6, Some errors, see below

(require typed/rackunit)

;;> Please leave a progress comment as per syllabus

; struct for all types of expressions our ZNQR language can interpret
(define-type ExprC (U numC ifC binopC IdC strC lamC AppC))
(struct numC ([n : Real]) #:transparent)
;(struct ifC ([x : ExprC] [y : ExprC] [exp : ExprC]) #:transparent)
(struct binopC ([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct ifC ([if : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct strC ([str : String]) #:transparent)
(struct lamC ([params : (Listof Symbol)] [body : ExprC]) #:transparent)

; FundefC structure
(struct FundefC ([name : Symbol] [args : (Listof Symbol)] [body : ExprC]) #:transparent)
(define double (FundefC 'double '(x) (binopC '+ (IdC 'x) (IdC 'x))))
(define fds (list double))

(struct Binding ([name : Symbol] [val : value]) #:transparent)
;(define-type Env (Immutable-HashTable Symbol value))
(define-type Env (Listof Binding))
(define mt-env '())
(define extend-env cons)

(define-type value (U numV boolV strV cloV primV))
(struct numV ([num : Real]) #:transparent)
(struct boolV ([bool : Boolean]) #:transparent)
(struct strV ([str : String]) #:transparent)
(struct cloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primV ([op : (-> value value value)]) #:transparent)
(struct funV ([name : Symbol] [params : (Listof Symbol)] [body : ExprC]) #:transparent)

; takes in a list of Sexpressions and returns them as a list of ExprC's
(define (parse-args [l : (Listof Sexp)]) : (Listof ExprC)
  (cond
    [(empty? l) '()]
    [else (cons (parse (first l)) (parse-args (rest l)))]))

; takes in a var and reformats it to -> syntax
(define (parse-var [args : (Listof Sexp)] [ids : (Listof Symbol)] [vals : (Listof Sexp)]) : (Listof Sexp)
  (match (first args)
    ;;> forgot to check for valid symbols here
    [(list (? symbol? id) '= val) (parse-var (rest args) (append ids (list id)) (append vals (list val)))]
    [else (append (list (list ids '-> (first args))) vals)]))

; finds duplicates in a list
(define (findDuplicates [lst : (Listof Symbol)]) : Boolean
  (cond ((null? lst) #f)
        ((member (car lst) (cdr lst)) #t)
        (else (findDuplicates (cdr lst)))))

(check-equal? (findDuplicates (list 'a 'b 'c)) #f)
(check-equal? (findDuplicates (list 'a 'a 'c)) #t)

; parser that reads in different data-types and turns them into our AST
(define (parse [a : Sexp]) : ExprC
  (match a
    [(? real? n) (numC n)]
    [(? string? str) (strC str)]
    [(? symbol? sym)
     (if (or (equal? sym 'var) (or (equal? sym 'if) (or (equal? sym '->) (equal? sym '=))))
         (error 'ZNQR "incorrect ID")
         (IdC sym))]
    [(list (list (? symbol? id) ...) val) ;(if (eq? (findDuplicates (cast id (Listof Symbol))) #t)
                                           ;   (error 'ZNQR "duplicate ids")
                                              (lamC (cast id (Listof Symbol)) (parse val))]
    [(list (list (? symbol? ids) ...) '-> body) (if (eq? (findDuplicates (cast ids (Listof Symbol))) #t)
                                                (error 'ZNQR "duplicate ids")
                                                (lamC (cast ids (Listof Symbol)) (parse body)))]
    [(list (list ids '-> body) vals ...)
     (match ids
       [(list (? symbol? id) ...) (if (or (< (length id) (length vals)) (> (length id) (length vals)))
                                      (error 'ZNQR "invalid arguments")
                                      (if (eq? (findDuplicates (cast id (Listof Symbol))) #t)
                                              (error 'ZNQR "duplicate ids")
                                              (AppC (lamC (cast id (Listof Symbol))
                                                          (parse body)) (parse-args vals))))])]
       ;[(list (? symbol?) id) (AppC (lamC (cast id (Listof Symbol))
        ;                                  (parse body)) (parse-args vals))])]
    [(list 'if test then else) (ifC (parse test) (parse then) (parse else))]
    ;;> need to make sure var has a body
    [(list 'var vals ...) (parse (parse-var vals '() '()))]
    [(list (? symbol? sym) args ...) (AppC (parse sym) (parse-args args))]
    [(list a) (AppC (parse a) '())]
    [else (error 'ZNQR "incorrect ZNQR3 syntax")]))

(check-equal? (parse (quote ((g) 15))) (lamC '(g) (numC 15)))
(check-equal? (parse '((var (y = 9) (f 3))))
              (AppC (AppC (lamC '(y) (AppC (IdC 'f) (list (numC 3)))) (list (numC 9))) '()))
(check-exn (regexp (regexp-quote "duplicate ids")) (lambda () (parse '((x x) -> 3))))
(check-exn (regexp (regexp-quote "duplicate ids")) (lambda () (parse '(var (z = (() -> 3)) (z = 9) (z)))))
(check-exn (regexp (regexp-quote "incorrect ZNQR3 syntax")) (lambda () (parse '((3 4 5) 4 i -> -> 6))))
(check-equal? (parse (quote ((a x y) -> ((w) -> (+ z (w y))))))
              (lamC '(a x y) (lamC '(w) (AppC (IdC '+) (list (IdC 'z) (AppC (IdC 'w) (list (IdC 'y))))))))
(check-equal? (parse 3) (numC 3))
(check-equal? (parse "hello") (strC "hello"))
(check-equal? (parse 'okay) (IdC 'okay))
(check-exn (regexp (regexp-quote "incorrect ID")) (lambda () (parse '=)))
(check-exn (regexp (regexp-quote "invalid arguments")) (lambda () (parse '((() -> 9) 17))))
(check-equal? (parse '(if (<= 3 5) 3 6)) (ifC (AppC (IdC '<=) (list (numC 3) (numC 5))) (numC 3) (numC 6)))
(check-equal? (parse '{var {z = {+ 9 14}} {y = 8} {+ z y}})
              (AppC (lamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (numC 9) (numC 14))) (numC 8))))
(define x (parse '{var {z = {+ 9 14}} {y = 8} {+ z y}}))
(define y '{var {z = {+ 9 14}} {y = 8} {+ z y}})

; takes in a symbol and its environment and returns the value that represents it
(define (id-lookup [for : Symbol] [env : Env]) : value
  (cond
    [(empty? env) (error 'ZNQR "id not found")]
    [else (cond
            [(equal? for (Binding-name (first env))) (Binding-val (first env))]
            [else (id-lookup for (rest env))])]))
(check-exn (regexp (regexp-quote "id not found")) (lambda () (id-lookup 'yee '())))

; operation for checking if two values are equal
(define (primequal? [l : value] [r : value]) : boolV
  (match l
    [(numV x) (if (numV? r) (boolV (eq? x (numV-num r))) (boolV #f))]
    [(strV str) (if (strV? r) (boolV (equal? str (strV-str r))) (boolV #f))]
    [(boolV x) (if (boolV? r) (boolV (eq? x (boolV-bool r))) (boolV #f))]))

(check-equal? (primequal? (numV 3) (numV 3)) (boolV #t))
(check-equal? (primequal? (numV 3) (strV "hi")) (boolV #f))
(check-equal? (primequal? (strV "hello") (strV "hello")) (boolV #t))
(check-equal? (primequal? (strV "hello") (numV 1)) (boolV #f))
(check-equal? (primequal? (boolV #t) (boolV #t)) (boolV #t))
(check-equal? (primequal? (boolV #t) (numV 3)) (boolV #f))

; operatin for checking less than or equal
(define (leq [l : value] [r : value]) : boolV
  (match l
    [(numV x)
     (match r
       [(numV y) (boolV (<= x y))])]))

; operation for adding primV
(define (primplus [l : value] [r : value]) : numV
  (match l
    [(numV x)
     (match r
       [(numV y) (numV (+ x y))]
       [else (error 'ZNQR "invalid prim args")])]
    [else (error 'ZNQR "invalid prim args")]))
(check-exn (regexp (regexp-quote "invalid prim args")) (lambda () (primplus (strV "+") (numV 2))))
(check-exn (regexp (regexp-quote "invalid prim args")) (lambda () (primplus (numV 2) (strV "+"))))

; operation for multiplying primV
(define (primmult [l : value] [r : value]) : value

  (match l
    [(numV x)
     (match r
       [(numV y) (numV (* x y))]
       [else (error 'ZNQR "invalid prim args")])]
    [else (error 'ZNQR "invalid prim args")]))

(check-exn (regexp (regexp-quote "invalid prim args")) (lambda () (primmult (strV "+") (numV 2))))
(check-exn (regexp (regexp-quote "invalid prim args")) (lambda () (primmult (numV 2) (strV "+"))))

; ; operation for subtracting primV
(define (primminus [l : value] [r : value]) : numV
  (match l
    [(numV x)
     (match r
       [(numV y) (numV (- x y))])]))

; operation for dividing primV
(define (primdiv [l : value] [r : value]) : numV
  (match l
    [(numV x)
     (match r
       [(numV y) (numV (/ x y))])]))

; extends our closure to contain multiple identifiers and functions
(define (extend-all [args : (Listof Symbol)] [vals : (Listof ExprC)] [env : Env]) : Env
  (cond
    [(empty? args) env]
    [else (extend-all (rest args) (rest vals)
                      ;;> this is an error you interp in the env as so,but extend on the clo env
                      (extend-env (Binding (first args) (interp (first vals) env)) env))]))



;;> interp should be at the top as per syllabus
; interprets all of our datatypes and returns the value the user requests in our language
(define (interp [a : ExprC] [env : Env]) : value
  (match a
    [(numC n) (numV n)]
    [(lamC a b) (cloV a b env)]
    [(ifC test then else)
     (cond
       [(equal? (interp test env) (boolV #t)) (interp then env)]
       [(equal? (interp test env) (boolV #f)) (interp else env)]
       [else (error 'ZNQR "incorrect use of if")])]
    [(AppC fun arg)
     (match (interp fun env)
       [(primV op) (cond
                     [(eq? (length arg) 2) (if (and (equal? op primdiv) (equal? (interp (second arg) env) (numV 0)))
                                               (error 'ZNQR "cannot divide by 0")
                                               (op (interp (first arg) env) (interp (second arg) env)))]
                     [else (error 'ZNQR "wrong number of primitive arguments")])]
       [(cloV params body clo-env)
         (define new-env (append (extend-all params arg env) clo-env))
         (interp body new-env)])]
    [(IdC temp) (id-lookup temp env)]))
    ;[(primV op) (error 'ZNQR "should not be getting here")]))

(define bind1 (Binding 'six (cloV  '() (numC 6) '())))
(define bind2 (Binding 'five (numV 5)))
(define plus (Binding '+ (primV primplus)))
(define true (Binding 'true (boolV #t)))
(define false (Binding 'false (boolV #f)))
(define mult (Binding '* (primV primmult)))
(define lequ (Binding '<= (primV leq)))
(define minus (Binding '- (primV primminus)))
(define divide (Binding '/ (primV primdiv)))
(define top-env (extend-env plus
                 (extend-env mult
                 (extend-env divide
                 (extend-env minus
                 (extend-env bind2
                 (extend-env lequ
                 (extend-env true
                 (extend-env false
                 (extend-env bind1 mt-env))))))))))

;(check-exn (regexp (regexp-quote "id already exists"))
 ;          (lambda () (extend-all (list '+) (list (numC 3)) top-env)))
;(check-exn (regexp (regexp-quote "should not be getting here"))
 ;          (lambda () (interp (primV primplus) top-env)))
(check-exn (regexp (regexp-quote "wrong number of primitive arguments"))
           (lambda () (interp (AppC (IdC '+) (list (numC 3) (numC 4) (numC 5))) top-env)))
;(check-equal? (interp x top-env) (numV 31))
(check-equal? (interp (ifC (AppC (IdC '<=) (list (numC 3) (numC 4))) (numC 3) (numC 4)) top-env)
              (numV 3))
(check-equal? (interp (ifC (AppC (IdC '<=) (list (numC 5) (numC 4))) (numC 3) (numC 4)) top-env)
              (numV 4))
(check-equal? (interp (AppC (IdC '+) (list (numC 10) (AppC (IdC 'six) '()))) top-env)
              (numV 16))
(check-equal? (interp (AppC (IdC '*) (list (numC 10) (IdC 'five))) top-env)
              (numV 50))
(check-equal? (interp (AppC (IdC '-) (list (numC 10) (IdC 'five))) top-env)
              (numV 5))
(check-equal? (interp (AppC (IdC '/) (list (numC 10) (IdC 'five))) top-env)
              (numV 2))
(check-equal? (interp (AppC (IdC '<=) (list (numC 10) (numC 11))) top-env)
              (boolV #t))

; takes in a value and returns it as a string
(define (serialize [val : value]) : String
  (match val
    [(numV x) (~v x)]
    [(strV str) (~v str)]
    [(boolV #t) "true"]
    [(boolV #f) "false"]
    [(cloV params body env) "#<procedure>"]
    [(primV op) "#<primop>"]))
(check-equal? (serialize (numV 9)) "9")
(check-equal? (serialize (strV "hi")) "\"hi\"")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize (boolV #f)) "false")
(check-equal? (serialize (primV primplus)) "#<primop>")
(check-equal? (serialize (cloV (list 'a 'b) (numC 3) top-env)) "#<procedure>")

(define add (FundefC 'add '(x y) (binopC '+ (IdC 'x) (IdC 'y))))
(define add3 (FundefC 'add3 '(x y z) (binopC '+ (IdC 'x) (binopC '+ (IdC 'y) (IdC 'z)))))
(define six (FundefC 'six '() (numC 6)))
(define test (list add double add3 six))

; accepts a Sexp and calls the parser and then the interp function to return the output
(define (top-interp [a : Sexp]) : String
  (serialize (interp (parse a) top-env)))

;(check-exn (regexp (regexp-quote "id's cannot be prim id's"))
 ;          (lambda () (extend-all (list '+) (list (numC 3)) top-env)))

(check-equal? (top-interp y) "31")
(check-exn (regexp (regexp-quote "incorrect use of if"))
           (lambda () (top-interp '(if (+ 4 3) 7 8))))
(check-exn (regexp (regexp-quote "cannot divide by 0"))
           (lambda () (top-interp '(/ 3 0))))



