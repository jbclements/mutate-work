#lang typed/racket
;Progress Comment: We were able to complete all parts of the assignment


(require typed/rackunit)

(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))

;ExprC Language
(define-type ExprC (U numC appC idC ifC boolC lamC stringC))
(tstruct numC ([n : Real]))
;;> boolC should not exist. Instead, it should be a binding in the top environment.
(tstruct boolC ([b  : Boolean]))
(tstruct ifC ([x : ExprC] [then : ExprC] [else : ExprC]))
(tstruct appC ([f : ExprC] [arg : (Listof ExprC)]))
(tstruct idC ([x : Symbol]))
(tstruct lamC ([args : (Listof ExprC)] [body : ExprC]))
(tstruct stringC ([s : String]))

;Binding and Env definition
(tstruct Binding ([name : ExprC] [val : Value]))
(define-type Env (Listof Binding))
(define mt-env
  '())
(define extend-env cons)

;bind : Symbol Real -> Binding
;Creates a Binding using a symbol and value
(define (bind [s : ExprC] [r : Value]) : Binding
  (Binding s r))

;Value definition
(define-type Value (U numV boolV closV primV stringV))
(tstruct numV ([n : Real]))
(tstruct boolV ([b : Boolean]))
(tstruct closV ([args : (Listof ExprC)] [body : ExprC] [env : Env]))
(tstruct primV ([op : Symbol]))
(tstruct stringV ([s : String]))

;top-level environment
;;> you are missing the true and false bindings in the top-env
;;> ie (bind 'true #t) (bind 'false #f)
;;> also, you could just use (list (bind a b) ...) to avoid the cons / extend-env
(define top-env (extend-env (bind (idC '+) (primV '+))
                      (extend-env (bind (idC '-) (primV '-))
                                (extend-env (bind (idC '*) (primV '*))
                                         (extend-env (bind (idC '/) (primV '/))
                                             (extend-env (bind (idC '<=) (primV '<=))
                                                  (extend-env (bind (idC 'equal?) (primV 'equal?))
                                                     (extend-env (bind (idC 'error) (primV 'error)) '()))))))))

;mock top-level environment for code coverage
(define mock-top-env (extend-env (bind (idC '+) (primV '+))
                      (extend-env (bind (idC '-) (primV '-))
                                (extend-env (bind (idC '*) (primV '*))
                                         (extend-env (bind (idC '/) (primV '/))
                                                      (extend-env (bind (idC '<=) (primV '<=))
                                                            (extend-env (bind (idC 'equal?) (primV 'equal?))
                                                                (extend-env (bind (idC 'foo) (primV 'bar)) '()))))))))

;do-many-parse : (Listof Symbol) -> ExprC
;does parse on every element in a list of symbols
(define (do-many-parse [syms : (Listof Symbol)]) : (Listof ExprC)
  (match syms
    ['() '()]
    [(cons f r) (cons (parse f) (do-many-parse r))]))

;extract-args-names : Sexp -> (Listof ExprC)
;extracts the local variables' Sexpressions and parses their names as a list of idC's
(define (extract-args-names [s : Sexp]) : (Listof ExprC)
  (match s
    ['() '()]
    [(cons f r) (match f
                  [(list (? legal-symbol? s) '= body) (cons (idC s) (extract-args-names r))]
                  [else (error 'extract-args-names "JILI not a legal local var name ~e" s)])]))

;extract-args-bodies : Sexp -> (Listof ExprC)
;extracts the local variables' bodies
(define (extract-args-bodies [s : Sexp]) : (Listof ExprC)
  (match s
    ['() '()]
    [(cons f r) (match f
                  [(list (? symbol? s) '= body) (cons (parse body) (extract-args-bodies r))])]))

;Helper function for parse to check for a legal if statement
;legal-expr? : Sexp -> Boolean
(define (legal-expr? [s : Sexp]) : Boolean
  (match s
    ['if #f]
    [other #t]))

;check-dups? : (Listof Sexp) -> Boolean
;Helper function to see if multiple args have the same name. returns true if there is a duplicate
(define (check-dups? [s : (Listof Any)]) : Boolean
  (match s
    ['() #f]
    [(cons f r) (cond
                  [(check-rest-list f r) #t]
                  [else (check-dups? r)])]))

;check-rest-list : Sexp (Listof Sexp) -> Boolean
;Helper function to compare an arg to the rest in the arg list. if returns true that means theres a duplicate.
(define (check-rest-list [s : Any] [lst : (Listof Any)]) : Boolean
  (match lst
    ['() #f]
    [(cons f r) (cond
                  [(equal? s f) #t]
                  [else (check-rest-list s r)])]))

;Helper function for parse to check for a legal symbol Ex: not an if
;legal-operand : Sexp -> Boolean
(: legal-symbol? (Any -> Boolean : #:+ Symbol))
(define (legal-symbol? s)
  (and (symbol? s)
  (not (equal? 'if s))
  (not (equal? '=> s))
  ;;> pretty sure this is redundant, because if it's a symbol it can't be a real...
  (not (real? s))
  (not (equal? 'in s))))

;parse : Sexp -> ExprC
;parses an expression
(define (parse [s : Sexp]) : ExprC
  (match s
    ;;> as mentioned above, the true and false should be idC's to be looked up in the top-env ... not a boolC
    ['true (boolC true)]
    ['false (boolC false)]
    [(list 'if x then else) (ifC (parse x) (parse then) (parse else))]
    [(? legal-symbol? x) (idC x)]
    [(? real? n) (numC n)]
    [(? string? s) (stringC s)]
    [(list (? symbol? s) ... '=> body) (cond
                                       [(check-dups? s) (error 'parse "JILI found dups ~e" s)]
                                       [else (lamC (do-many-parse (cast s (Listof Symbol))) (parse body))])]
    [(list 'var args 'in body) (cond
                                 [(check-dups? (extract-args-names args))
                                  (error 'parse "JILI found local variable dups ~e" args)]
                                 [else
                                  (appC (lamC (extract-args-names args) (parse body)) (extract-args-bodies args))])]
    [(list (? legal-expr? expr) expr2 ...) (appC (parse expr) (map parse expr2))]
    [other (error 'parse "JILI failed to parse ~e" s)]))


(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (parse '{{b a b b => {+ 1 b}} 0 1 2 3})))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (parse '{{b b => {+ b b}} 3 4})))

(check-equal? (parse '{{a b => {+ a b}} 3 4})
              (appC
               (lamC (list (idC 'a) (idC 'b))
                     (appC (idC '+) (list (idC 'a) (idC 'b)))) (list (numC 3) (numC 4))))
(check-equal? (parse '{{a => a} 1})
              (appC (lamC (list (idC 'a)) (idC 'a)) (list (numC 1))))
(check-equal? (parse '{{a => a} true})
              (appC (lamC (list (idC 'a)) (idC 'a)) (list (boolC true))))
(check-equal? (parse '{{a => a} false})
              (appC (lamC (list (idC 'a)) (idC 'a)) (list (boolC false))))
(check-equal? (parse '{var {[z = {+ 9 14}]
                            [y = 98]}
                       in
                            {+ z y}})
              (appC (lamC (list (idC 'z) (idC 'y)) (appC (idC '+) (list (idC 'z) (idC 'y))))
                    (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (parse '{{a b => {if {+ a b}}} 0 0})))


;check-if-num : Value -> Boolean
;checks if the argument of an primop is a number
(define (check-if-num [l : Value]) : Real
  (match l
    [(numV n) n]
    [other (error 'check-if-num "JILI not a number ~e" l)]))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (check-if-num (boolV true))))



;env-lookup : Env Symbol -> Val
;looks through the given environment for the given symbol and returns that binding's value
(define (env-lookup [env : Env] [n : ExprC]) : Value
  (match env
    ['() (error 'env-lookup "JILI no symbol exists ~e" n)]
    [(cons f r) (cond
                  [(equal? n (Binding-name f)) (Binding-val f)]
                  [else (env-lookup r n)])]))

;mult-extend-env : Env (Listof Symbol) (Listof Real) -> Env
;adds multiple args to the env
(define (mult-extend-env [env : Env] [s : (Listof ExprC)] [n : (Listof Value)]) : Env
  (match s
    ['() (match n
           ['() env]
           [else (error 'mult-extend-env "JILI Too many reals not enough symbols ~e" n)])]
    [(cons f r) (match n
                  ;;> technically the values don't have to be reals right? They could be other things too
                  ['() (error 'mult-extend-env "JILI Too many symbols not enough reals ~e" n)]
                  [(cons g h) (extend-env (bind f g) (mult-extend-env env r h))])]))

;serialize : Value -> String
;takes a value and turns it into a string
(define (serialize [v : Value]) : String
  (match v
    [(numV n) (~v n)]
    [(boolV b) (cond
                 [(equal? true b) "true"]
                 [(equal? false b) "false"])]
    [(primV p) "#<primop>"]
    [(closV a b c) "#<procedure>"]
    [(stringV s) (~v s)]))

(check-equal? (serialize (numV 2)) "2")
(check-equal? (serialize (boolV true)) "true")
(check-equal? (serialize (boolV #f)) "false")

;interp : ExprC (listof FundefC) -> Real
;Interprets the given expression using the list of funs to resolve applications
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(numC n) (numV n)]
    ;;> as mentioned above, boolC should not be a type
    [(boolC b) (boolV b)]
    [(stringC s) (stringV s)]
    [(ifC x then else) (match (interp x env)
                         [(boolV b) (if b (interp then env) (interp else env))]
                         [else 'interp (error "JILI does not evaluate to bool ~e" x)])]
    [(idC n) (env-lookup env (idC n))]
    [(lamC args body) (closV args body env)]
    [(appC f a) (define f-value (interp f env))
           (define arglst (interp-arg-list a env))
           (match f-value
              [(primV p) (match a
                      ['() (primV p)]
                      [(cons l (cons r '())) (cond
                            [(equal? '+ p) (numV (+ (check-if-num (interp l env)) (check-if-num (interp r env))))]
                            [(equal? '- p) (numV (- (check-if-num (interp l env)) (check-if-num (interp r env))))]
                            [(equal? '* p) (numV (* (check-if-num (interp l env)) (check-if-num (interp r env))))]
                            [(equal? '/ p) (numV (cond
                                                      [(not (equal? (check-if-num (interp r env)) 0))
                                                       (/ (check-if-num (interp l env)) (check-if-num (interp r env)))]
                                                      [else (error 'interp "JILI divide by zero ~e" p)]))]
                            [(equal? '<= p) (boolV (<= (check-if-num (interp l env)) (check-if-num (interp r env))))]
                            [(equal? 'equal? p) (boolV (equal? (interp l env) (interp r env)))]
                            [else error (error 'interp "JILI how possible? ~e" p)])]
                      [str (error 'interp "JILI user-error ~e" str)])]
               [(closV cargs cbody cenv) (interp cbody
                        (mult-extend-env cenv cargs arglst))]
               [other 'interp (error "JILI non closure ~e" f-value)])]))

;interp-arg-list : (Listof ExprC) (Listof FundefC) Env : (Listof Real)
;helper function to interp in every argument in a function call
(define (interp-arg-list [arglst : (Listof ExprC)] [env : Env]) : (Listof Value)
  (match arglst
    ['() '()]
    [(cons f r) (cons (interp f env) (interp-arg-list r env))]))

(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (interp (appC (numC 4) (list (numC 2))) top-env)))
(check-equal? (interp (boolC #t) top-env) (boolV true))
(check-equal? (interp (appC (idC '+) '()) top-env) (primV '+))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (interp (appC (numC 4) (list (numC 2))) top-env)))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (interp (appC (idC 'foo) (list (numC 2) (numC 2))) mock-top-env)))

;top-interp : Sexp -> Real
;Calls both parsing the Sexp and interp
(define (top-interp [fun-sexps : Sexp]) : String
  (serialize (interp (parse fun-sexps) top-env)))

;Assignment 5 test cases
(check-equal? (top-interp '{{a => a} 1})
              "1")
(check-equal? (top-interp '{{a b => {+ a b}} 3 4})
              "7")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {+ a b}} 3 4})
              "7")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {- a b}} 3 4})
              "-1")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {* a b}} 3 4})
              "12")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {/ a b}} 4 4})
              "1")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {<= a b}} 3 4})
              "true")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {equal? a b}} 3 4})
              "false")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {equal? a b}} "hi" "hi"})
              "true")
(check-equal? (top-interp '{{f a b => {f a b}} {a b => {equal? a b}} 3 "hi"})
              "false")
(check-equal? (top-interp '{{a b => {if {<= a b} 1 2}} 0 0})
              "1")
(check-equal? (top-interp '{{a b => {if {<= a b} 1 2}} 2 0})
              "2")
(check-equal? (top-interp '{var {[z = {+ 9 14}]
                            [y = 98]}
                       in
                            {+ z y}})
              "121")

(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (top-interp '{{a b => {if {+ a b} 1 2}} 0 0})))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (top-interp '{{a b => {/ a b}} 0 0})))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (top-interp '{sadf{a b => {/ a b}} 0 0})))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (top-interp '{{a b => {/ a b}} 0 #t})))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (top-interp '{{a b => {if {+ a b} 1 2}} 0 0 0})))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (top-interp '{{a b c => {if {+ a b} 1 2}} 0 0})))

(check-equal? (top-interp '(=> 9)) "#<procedure>")

(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (parse '(var ((z = (=> 3)) (z = 9)) in (z)))))
(check-exn (regexp (regexp-quote "JILI"))
;;> (AUTOCOMMENT) Grader: most of these are errors, but be sure to check whether this message is warranted:
;;> (AUTOCOMMENT) Error messages should display the incorrect program text; this makes them useful.
           (lambda () (top-interp '(error "1234"))))
(check-exn (regexp (regexp-quote "JILI"))
           (lambda () (parse '(var ((=> = "")) in "World"))))

(check-equal? (top-interp  '(if true "one" "two")) "\"one\"")
