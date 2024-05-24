;;> (AUTOCOMMENT) Apparently missing a required structure: '("primV" "PrimV" "Pri...
;;> Testfail: while evaluating (begin (parse (quote (if (=> (=> ((=> (var ((a = (=> (if (((var ((/ = ((if (var ((- = (var ((+ = (if (if true (true false null + => false) (- * / => "Hello")) (null (equal? <= => 0) ("World" (var ((true = +)) in (1 (if "" (var ((false = "Hello")) in (var ((null = -1)) in (if 2.2 (if (var () in "") - ((((var () in /) -22/7) "World") *)) (var () in 0)))) (if (var () in (a => (if (if <= a -1) 1 "World"))) "Hello" equal?)) b)) c d) e f) g))) in h)) (* = i)) in j) k l))) (equal? = m) (<= = n)) in o))) p q))) (b = r) (c = s) (d = t)) in u))))) v w))) #t):
;  broke its own contract
;  promised: list?
;  produced: ''u
;  in: (listof
;       (recursive-contract
;        (or/c
;         keyword?
;         string?
;         symbol?
;         char?
;         '()
;         #t
;         #f
;         (and/c
;          number?
;          ...eric-base-types.rkt:241:12)
;         (and/c
;          number?
;          ...eric-base-types.rkt:231:12)
;         (and/c
;          number?
;          ...eric-base-types.rkt:221:12)
;         (and/c
;          number?
;          ...eric-base-types.rkt:211:12)
;         (and/c
;          number?
;          (not/c real?)
;          ...eric-base-types.rkt:198:12)
;         (and/c
;          number?
;          (not/c real?)
;          ...eric-base-types.rkt:186:12)
;         (and/c single-flonum? negative?)
;         (and/c single-flonum? positive?)
;         g514
;         g515
;         (and/c
;          single-flonum?
;          ...eric-base-types.rkt:163:27)
;         (and/c flonum? negative?)
;         (and/c flonum? positive?)
;         g519
;         g520
;         (and/c
;          flonum?
;          ...eric-base-types.rkt:143:20)
;         (and/c
;          exact-rational?
;          negative?
;          (not/c integer?))
;         (and/c
;          exact-rational?
;          positive?
;          (not/c integer?))
;         (and/c
;          exact-integer?
;          negative?
;          (not/c fixnum?))
;         (and/c
;          exact-integer?
;          positive?
;          (not/c fixnum?))
;         (and/c fixnum? negative?)
;         (and/c fixnum? positive? (not/c index?))
;         (and/c index? positive? (not/c byte?))
;         g529
;         1
;         0
;         (box/c
;          (recursive-contract
;           g5856674538541
;           #:chaperone))
;         (vectorof
;          (recursive-contract
;           g5856674536540
;           #:chaperone)
;          #:immutable
;          #t)
;         (vectorof
;          (recursive-contract
;           g5856674538541
;           #:chaperone)
;          #:immutable
;          #f)
;         (cons/c
;          (recursive-contract
;           g5856674536540
;           #:chaperone)
;          (recursive-contract
;           g5856674536540
;           #:chaperone)))
;        #:chaperone))
;  contract from: cast
;  blaming: cast
;   (assuming the contract is correct)
;  at: #(struct:object:text% ...):29:62
;;> Testfail: expected exception with message containing JILI on test expression: '(parse '(var ((=> = "")) in "World"))
;;> Testfail: your code failed a test: (top-interp (quote (if true "one" "two"))) evaluated to "one", expecting "\"one\""

; I finished implementing the entire assignment but my parse is giving me issues for some reason.
;;> Thanks for the heads up!


#lang typed/racket
(require typed/rackunit)

(define-type ExprC (U NumC IdC StringC LamC CondC AppC))
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([x : Symbol]) #:transparent)
(struct StringC ([s : String]) #:transparent)
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct CondC ([if : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)

(struct Binding ([name : Symbol] [val : Value]) #:transparent)
(define-type Env (Listof Binding))

(struct CloV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(define-type Value (U Real Boolean String '+ '- '/ '* '<= 'equal? 'error CloV))


; Define top-level environment
;;> Why bind the priamtive symbols to themselves? What new information are those primative bindings adding to your code?
(define top-env (list (Binding '+ '+) (Binding '- '-) (Binding '/ '/) (Binding '* '*) (Binding '<= '<=)
                      (Binding 'equal? 'equal?) (Binding 'error 'error) (Binding 'true true) (Binding 'false false)))

; Desugars an Sexp to an Sexp
(define (desugar [s : Sexp]) : Sexp
  (match s
    [(list 'var (list (list a '= b) ...) 'in body)
     ;;> (AUTOCOMMENT) This cast introduces a bug.
     ;;> The second cast is promising a list, but really only can guarantee an Sexp.
     ;;> By using the cast, you may have made it work sometimes, but you made yourself
     ;;> a nasty bug later on. 
     (define inner (append (cast a (Listof Sexp)) '(=>) (list (cast body (Listof Sexp)))))
     (define outer (append (list inner) b))
     (cast outer Sexp)]))

; Parses an Sexp to an ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    ['() (error 'parse "JILI: empty s-exp")]
    [(? real? a) (NumC a)]
    [(? symbol? a)
     (cond
       [(equal? (is-restricted a) false) (IdC a)]
       ;;> (AUTOCOMMENT) Grader: most of these are errors, but be sure to check whether this message is warranted:
       ;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
       ;;> Try using (error 'error-type "error-description with a value: ~e" x)
       [else (error 'parse "JILI: incorrect Sexp formatting")])]
    [(? string? a) (StringC a)]
    [(? list? l)
     (match l
       [(list 'if a b c) (CondC (parse a) (parse b) (parse c))]
       [(list 'var (list (list a '= b) ...) 'in body) (parse (desugar s))]
       [(list (? symbol? a) ... '=>  b)
        (cond
          [(and (equal? (is-duplicates a) false) (equal? (is-restricted-list a) false))
           (LamC (cast a (Listof Symbol)) (parse b))]
          ;;> (AUTOCOMMENT) Grader: most of these are errors, but be sure to check whether this message is warranted:
          ;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
          ;;> Try using (error 'error-type "error-description with a value: ~e" x)
          [else (error 'parse "JILI: error with arguments")])]
       [(list a b ...)
        (AppC (parse a) (map parse b))])]))

; Determines if there are duplicates in a list
(define (is-duplicates [l : (Listof Any)]) : Boolean
  (cond
    [(equal? l '()) false]
    [(equal? (member (first l) (rest l)) false)
     (is-duplicates (rest l))]
    [else true]))



; Determines if something is a primitive or keyword
(define (is-prim [s : Any]) : Boolean
  (match s
    ['+ true]
    ['- true]
    ['/ true]
    ['* true]
    ['<= true]
    ['equal? true]
    ['error true]
    [else false]))

; Determines if a word is restricted
(define (is-restricted [s : Any]) : Boolean
  (match s
    ['if true]
    ['var true]
    ['in true]
    ['=> true]
    [else false]))


; Determines if a restricted word exists inside a list
(define (is-restricted-list [l : (Listof Any)]) : Boolean
  (match l
    ['() false]
    [other
     (cond
       [(equal? (is-restricted (first l)) true) true]
       [else (is-restricted-list (rest l))])]))


; Loop through an environment to look for a matching name, returning the corresponding value or throwing
; an error if the name is not found
(define (search-env [env : Env] [name : Symbol]) : Value
  (match env
    ['() (error 'interp "JILI: name not found in env")]
    [else (match (first env)
            [(Binding b-name b-val)
             (cond
               [(equal? b-name name) b-val]
               [else (search-env (rest env) name)])])]))


; Builds a list of bindings between a list of symbols and a list of values
(define (build-env [sList : (Listof Symbol)] [vList : (Listof Value)]) : Env
  (match sList
    ['() '()]
    [other (append (list (Binding (first sList) (first vList))) (build-env (rest sList) (rest vList)))]))


; Combines two environments except for duplicate bindings (new ones are prioritized)
(define (combine-env [old-env : Env] [new-env : Env]) : Env
  (append new-env old-env))


; Applies interp to a list of ExprCs and returns a list of Values
(define (interp-list [eList : (Listof ExprC)] [env : Env]) : (Listof Value)
  (match eList
    ['() '()]
    [other
     (append (list (interp (first eList) env)) (interp-list (rest eList) env))]))



; Interprets an ExprC into a Value using an environment
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(NumC n) n]
    [(IdC x) (search-env env x)]
    [(StringC s) s]
    [(LamC args body) (CloV args body env)]
    [(CondC if then else)
     (define interpreted-if (interp if env))
     (cond
       [(equal? (boolean? interpreted-if) false) (error 'interp "JILI: if does not eval to boolean")]
       [(equal? interpreted-if true) (interp then env)]
       [else
        (interp else env)])]
    [(AppC fun args)
     ; Interprets the fun and matches it to either CloV or primitives, equal?, and 'error
     (define interpreted-fun (interp fun env))
     (match interpreted-fun
       [(CloV clo-args clo-body clo-env)
        (cond
          [(equal? (length args) (length clo-args))
           (define new-env (build-env clo-args (interp-list args env)))
           (interp clo-body (combine-env clo-env new-env))]
          [else (error 'interp "JILI: num arguments incorrect")])]
       ['+
        (match args
          [(list a b)
           ;;> You defined these but never used them...
           (define a-interp (interp a env))
           (define b-interp (interp b env))
           (cond
             ;;> (AUTOCOMMENT) This cast introduces a bug. What if the exprC here evaluates to a string? You get a crash!
             [(and (real? a-interp) (real? b-interp)) (+ (cast (interp a env) Real) (cast (interp b env) Real))]
             [else (error 'interp "JILI: invalid args")])]
          [other (error 'interp "JILI: incorrect number of arguments for +")])]
       ['-
        (match args
          ;;> same as before.
          [(list a b)
           (define a-interp (interp a env))
           (define b-interp (interp b env))
           (cond
             [(and (real? a-interp) (real? b-interp)) (- (cast (interp a env) Real) (cast (interp b env) Real))]
             [else (error 'interp "JILI: invalid args")])]
          [other (error 'interp "JILI: incorrect number of arguments for -")])]
       ['*
        (match args
          ;;> same as before.
          [(list a b)
           (define a-interp (interp a env))
           (define b-interp (interp b env))
           (cond
             [(and (real? a-interp) (real? b-interp)) (* (cast (interp a env) Real) (cast (interp b env) Real))]
             [else (error 'interp "JILI: invalid args")])]
          [other (error 'interp "JILI: incorrect number of arguments for *")])]
       ['/
        (match args
          [(list a b)
           (define a-interp (interp a env))
           (define b-interp (interp b env))
           (cond
             [(and (real? a-interp) (real? b-interp))
              (cond
                [(equal? b-interp 0) (error 'interp "JILI: divide by zero error")]
                [else (/ a-interp b-interp)])]
             [else (error 'interp "JILI: invalid args")])]
          [other (error 'interp "JILI: incorrect number of arguments for /?")])]
       ['<=
        (match args
          ;;> same as before.
          [(list a b)
           (define a-interp (interp a env))
           (define b-interp (interp b env))
           (cond
             [(and (real? a-interp) (real? b-interp))
              (or (< (cast (interp a env) Real) (cast (interp b env) Real)) (= (cast (interp a env) Real)
                                                                               (cast (interp b env) Real)))]
             [else (error 'interp "JILI: invalid args")])]
          [other (error 'interp "JILI: incorrect number of arguments for <=")])]
       ['equal?
        (match args
          [(list a b)
           (cond
             [(and (equal? (is-prim (interp a env)) false) (equal? (is-prim (interp b env)) false))
              (equal? (interp a env) (interp b env))]
             [else (error 'interp "JILI: equal? must not contain closures or primitive operators")])]
          [other (error 'interp "JILI: incorrect number of arguments for equal?")])]
       ['error (error 'interp "JILI: user-error ~s" (serialize (first (interp-list args env))))]
       [else (error 'interp "JILI: incorrect formatting")]
;;> (AUTOCOMMENT) This line contains nothing but close parens:
       )]))


; Accepts any JILI5 value and returns a string
(define (serialize [val : Value]) : String
  (match val
    [(? real? n) (~v n)]
    [#t "true"]
    [#f "false"]
    [(? string? s) s]
    [(CloV a b c) "#<procedure>"]
    [other "#<primop>"]))


; Combines parsing and evaluation.
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))



;;> why



;;> all the




;;> white space?
(define compose-fun '{{compose =>

                               {{add1 =>

                                      {{add2 =>

                                             {add2 99}

                                             } {compose add1 add1}}

                                      } {x => {+ 1 x}}}


                               } {f g => {h => {f {g h}}}}})



; Test cases

(check-equal? (is-prim '+) true)
(check-equal? (is-prim '-) true)
(check-equal? (is-prim '/) true)
(check-equal? (is-prim '*) true)
(check-equal? (is-prim '<=) true)
(check-equal? (is-prim 'equal?) true)
(check-equal? (is-prim 'error) true)
(check-equal? (is-prim 'asdf) false)

(check-equal? (is-duplicates (list 3 3)) true)
(check-equal? (is-duplicates (list 3 5 6)) false)

(check-equal? (is-restricted 'if) true)
(check-equal? (is-restricted 'var) true)
(check-equal? (is-restricted 'in) true)
(check-equal? (is-restricted '=>) true)

(check-equal? (is-restricted-list (list 'if)) true)


(check-equal? (desugar '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}}) '((z y => (+ z y)) (+ 9 14) 98))

(check-equal? (parse '{a b c d}) (AppC (IdC 'a) (list (IdC 'b) (IdC 'c) (IdC 'd))))
(check-equal? (parse '{+ a b}) (AppC (IdC '+) (list (IdC 'a) (IdC 'b))))
(check-equal? (parse '{if {equal? "hello" 4} {+ 3 4} {* 3 x}}) (CondC
                                                                (AppC (IdC 'equal?) (list (StringC "hello") (NumC 4)))
                                                                (AppC (IdC '+) (list (NumC 3) (NumC 4)))
                                                                (AppC (IdC '*) (list (NumC 3) (IdC 'x)))))
(check-equal? (parse '{a => 7}) (LamC '(a) (NumC 7)))
(check-equal? (parse '{var {[z = {+ 9 14}] [y = 98]} in {+ z y}})
              (AppC (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))

(check-exn (regexp (regexp-quote  "JILI: incorrect Sexp formatting"))
           (lambda () (parse '(+ if 4))))

(check-exn (regexp (regexp-quote  "JILI: incorrect Sexp formatting"))
           (lambda () (parse '(=> 4 4))))

(check-exn (regexp (regexp-quote  "JILI: error with arguments"))
           (lambda () (parse '(x x => 3))))

(check-exn (regexp (regexp-quote  "JILI: incorrect Sexp formatting"))
           (lambda () (parse '(3 4 5 => 6))))

(check-exn (regexp (regexp-quote  "JILI: incorrect Sexp formatting"))
           (lambda () (parse 'if)))

(check-exn (regexp (regexp-quote  "JILI: empty s-exp"))
           (lambda () (parse '())))


(define poly-fun '(var {[f = {x => {* x x}}]}
                       in
                       {f 7}))

(define fact-fun '(var {[fact = {fact2 x => {if {equal? x 0} 1 {* x {fact2 fact2 {- x 1}}}}}]}
                       in
                       {fact fact 3}))


(define simp-fun '(var {[simp = {simp2 x => {if {equal? x 0} 0 {simp2 simp2 {- x 1}}}}]}
                       in
                       {simp simp 1}))

(check-equal? (interp (StringC "hello world") top-env) "hello world")
(check-equal? (interp (AppC (IdC '+) (list (NumC 3) (NumC 5))) top-env) 8)
(check-equal? (interp (AppC (IdC '/) (list (NumC 3) (NumC 1))) top-env) 3)
(check-equal? (interp (AppC (IdC '<=) (list (NumC 3) (NumC 5))) top-env) true)


(check-exn (regexp (regexp-quote  "interp: JILI: user-error \"This is my custom error\""))
           (lambda () (interp (AppC (IdC 'error) (list (StringC "This is my custom error"))) top-env)))


(check-exn (regexp (regexp-quote  "JILI: incorrect number of arguments for equal?"))
           (lambda () (interp (AppC (IdC 'equal?) (list (NumC 3) (NumC 2) (NumC 5))) top-env)))

(check-exn (regexp (regexp-quote  "JILI: equal? must not contain closures or primitive operators"))
           (lambda () (interp (AppC (IdC 'equal?) (list (IdC '+) (IdC '-))) top-env)))


(check-equal? (serialize true) "true")
(check-equal? (serialize false) "false")
(check-equal? (serialize "Hello") "Hello")
(check-equal? (serialize '+) "#<primop>")
(check-equal? (serialize (CloV '(+) (IdC 'x) top-env)) "#<procedure>")




(check-equal? (interp (parse simp-fun) top-env) 0)

(check-equal? (top-interp fact-fun) "6")


(check-equal? (search-env top-env 'equal?) 'equal?)


(check-equal? (interp (parse '{+ 3 5}) top-env) 8)
(check-equal? (interp (parse '{if {<= 3 5} 3 {+ 4 1}}) top-env) 3)
(check-equal? (interp (parse '{if {<= 6 5} 5 {+ 5 1}}) top-env) 6)
(check-equal? (interp (parse "Hello") top-env) "Hello")
(check-equal? (interp (parse '{{x => x} 2}) top-env) 2)


(check-equal? (top-interp '(var {[pow = {pow2 b n => {if {equal? n 0} 1 {* b {pow2 pow2 b {- n 1}}}}}]}
                                in
                                {pow pow 3 4})) "81")

(check-exn (regexp (regexp-quote  "JILI: num arguments incorrect"))
           (lambda () (top-interp '((=> 9) 17))))

(check-exn (regexp (regexp-quote  "JILI: if does not eval to boolean"))
           (lambda () (top-interp '(if (+ 4 3) 7 8))))

(check-exn (regexp (regexp-quote  "JILI: divide by zero error"))
           (lambda () (top-interp '(/ 1 (- 3 3)))))

(check-equal? (top-interp (quote ((+ => (* + +)) 14))) "196")

(check-exn (regexp (regexp-quote  "JILI: invalid args"))
           (lambda () (top-interp '(+ + +))))
(check-exn (regexp (regexp-quote  "JILI: invalid args"))
           (lambda () (top-interp '(- + +))))
(check-exn (regexp (regexp-quote  "JILI: invalid args"))
           (lambda () (top-interp '(* + +))))
(check-exn (regexp (regexp-quote  "JILI: invalid args"))
           (lambda () (top-interp '(/ + +))))
(check-exn (regexp (regexp-quote  "JILI: invalid args"))
           (lambda () (top-interp '(<= + +))))

(check-exn (regexp (regexp-quote  "interp: JILI: name not found in env"))
           (lambda () (top-interp '((ignoreit => (ignoreit (/ 1 0))) (lam ignoreit (x) (+ 3 4))))))

(check-exn (regexp (regexp-quote  "interp: JILI: name not found in env"))
           (lambda () (top-interp 'abcd)))

(check-exn (regexp (regexp-quote  "interp: JILI: name not found in env"))
           (lambda () (top-interp '((var ((y = 9)) in (f 3))))))

(check-exn (regexp (regexp-quote  "JILI: incorrect number of arguments for +"))
           (lambda () (top-interp '(+ 1 2 3))))

(check-exn (regexp (regexp-quote  "JILI: incorrect number of arguments for -"))
           (lambda () (top-interp '(- 1 2 3))))

(check-exn (regexp (regexp-quote  "JILI: incorrect number of arguments for *"))
           (lambda () (top-interp '(* 1 2 3))))

(check-exn (regexp (regexp-quote  "JILI: incorrect number of arguments for /"))
           (lambda () (top-interp '(/ 1 2 3))))

(check-exn (regexp (regexp-quote  "JILI: incorrect number of arguments for <="))
           (lambda () (top-interp '(<= 1 2 3))))

(check-exn (regexp (regexp-quote  "JILI: incorrect formatting"))
           (lambda () (top-interp '(((=> 3)) 4 5))))



