#lang typed/racket

;;> eyeball: 6/6, Very nice

(require typed/rackunit)

;; GOAL: Implement an interpreter for a higher-order language including booleans, strings, and local variable bindings.

;;ZNQR3 Grammar
;Exper = Num
;    |    id --------
;    |    String ---------
;    |    {if Expr Expr Expr} ---------
;    |    {var {id = Expr} ... Expr} --------
;    |    {{id ...} -> Expr} -----------
;    |    {Expr Expr ...} ---- primitives and functions. Do more test cases to ensure shadowing works.
; ... where an id is not var, if, lam, or =.


;; Structures for the ZNQR language
(define-type ExprC (U numC idC ifC appC strC lamC))
(struct numC ([n : Real]) #:transparent)
(struct idC ([v : Symbol]) #:transparent)
(struct ifC ([exp : ExprC] [thn : ExprC] [els : ExprC]) #:transparent)
(struct appC ([exp : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct strC ([str : String]) #:transparent)
(struct lamC ([ids : (Listof Symbol)] [body : ExprC]) #:transparent)

;; VALUES
(define-type Value (U Real Boolean String prim closure))
(struct prim ([func : (Value Value -> Value)]) #:transparent)
(struct closure ([func : lamC] [parentEnv : Env]) #:transparent)

;; Setup for environment
(define-type Env (Listof Binding))
(struct Binding ([name : Symbol] [val : Value]) #:transparent)

;; These bindings will always be available in a program, unless redefined. Similar to rackets +, -
(define top-env (list
                 (Binding 'true #t)
                 (Binding 'false #f)

                 (Binding '+ (prim (λ ([a : Value] [b : Value])
                                     (if (or (not (real? a))
                                             (not (real? b)))
                                         (error 'ZNQR "Expected two reals for + operator. Given\t~e ~e"
                                                (serialize a) (serialize b))
                                         (+ a b)))))

                 (Binding '- (prim (λ ([a : Value] [b : Value])
                                     (if (or (not (real? a))
                                             (not (real? b)))
                                         (error 'ZNQR "Expected two reals for - operator. Given\t~e ~e"
                                                (serialize a) (serialize b))
                                         (- a b)))))

                 (Binding '* (prim (λ ([a : Value] [b : Value])
                                     (if (or (not (real? a))
                                             (not (real? b)))
                                         (error 'ZNQR "Expected two reals for * operator. Given\t~e ~e"
                                                (serialize a) (serialize b))
                                         (* a b)))))

                 (Binding '/ (prim (λ ([a : Value] [b : Value])
                                     (cond
                                       [(or (not (real? a)) (not (real? b)))
                                        (error 'ZNQR "Expected two reals for / operator. Given\t~e ~e"
                                               (serialize a) (serialize b))]
                                       [(= 0 b) (error 'ZNQR "Divide by 0 exception.")]
                                       [else (/ a b)]))))

                 (Binding '<= (prim (λ ([a : Value] [b : Value])
                                      (if (or (not (real? a))
                                              (not (real? b)))
                                          (error 'ZNQR "Expected two reals for <= operator. Given\t~e ~e"
                                                 (serialize a) (serialize b))
                                          (<= a b)))))

                 (Binding 'equal? (prim (λ ([a : Value] [b : Value]) (equal? a b))))))


;; Reserved Keywords
(define keywords (make-immutable-hash (list
                                       (cons 'var 'var)
                                       (cons 'if 'if)
                                       (cons '-> '->)
                                       (cons '= '=))))

;; ------------------------------------------------------- PARSER ------------------------------------------------------
;; This function will take in an Sexpr and return an ExprC expression
(: parse (Sexp -> ExprC))
(define (parse s)
  (match s
    [(? real?) (numC s)]
    [(? string?) (strC s)]
    [(? symbol? id) #:when (hash-has-key? keywords id) (error 'ZNQR "Cannot use Keyword ~e as an identifier" id)]
    [(? symbol? id) (idC id)]
    [(list 'if exp thn els) (ifC (parse exp) (parse thn) (parse els))]
    [(list 'if exp thn) (error 'ZNQR "if: missing an else expression.\t~e" s)]
    [(list 'if _ ...) (error 'ZNQR "if: bad syntax.\t~e" s)]
    [(list 'var (list ids '= Exprs) ...) (error 'ZNQR "Missing var body.\t~e" s)]
    [(list 'var (list ids '= Exprs) ... body)
     (cond
       [(not (andmap symbol? ids)) (error 'ZNQR "variable ids must be symbols.")]
       [(check-duplicates ids) (error 'ZNQR "Duplicate variables.")]
       [(check-keywords ids)
        => (lambda (id) (error 'ZNQR "cannot use Keyword ~e as identifier." (first ids)))]
       [else (appC (lamC ids (parse body)) (map parse (cast Exprs (Listof Sexp))))])]
    [(list (list ids ...) '-> body)
     (cond
       [(not (andmap symbol? ids)) (error 'ZNQR "Function parameters must be symbols.\t~e" s)]
       [(check-duplicates ids) (error 'ZNQR "Duplicate variables ~e." ids)]
       [(check-keywords ids)
        => (lambda (id) (error 'ZNQR "cannot use Keyword ~e as identifier." (first ids)))]
       [else (lamC ids (parse body))])]
    [(list func args ...) (appC (parse func) (map parse args))]
    ))


(: check-keywords
   ((Listof Symbol) -> (U Symbol Boolean)))
(define (check-keywords ids)
  (cond
    [(empty? ids) #f]
    [(hash-has-key? keywords (first ids)) (first ids)]
    [else (check-keywords (rest ids))]))


;----------------------------------------------------------------------------------------------------------------------

;; looks up a variable id in the enviornment
(: lookup
   (Symbol Env -> Value))
(define (lookup id env)
  (cond
    [(empty? env) (error 'ZNQR "id ~e not found." id)]
    [(equal? id (Binding-name (first env))) (Binding-val (first env))]
    [else (lookup id (rest env))]))


;; -------------------------------------------------- INTERPRETER -----------------------------------------------------
;; will take in an AST and ouput value(s) and evaluates an ArithC expression and returns a Real number.
(: interp
   (ExprC Env -> Value))
(define (interp exp env)
  (match exp
    [(numC n) n]
    [(strC str) str]
    [(idC id) (lookup id env)]
    [(ifC exp thn els)
     (match (interp exp env)
       [#t (interp thn env) ]
       [#f (interp els env)]
       [else (error 'ZNQR "if guard should evaluate to a boolean!")])]
    [(lamC ids body) (closure exp env)]
    [(appC op args)
     (define func (interp op env))
     (match func
       [(prim func)
        (define arg-vals (map (λ ([arg : ExprC]) (interp arg env)) args))
        (cond
          [(= 2 (length args)) (func (first arg-vals) (second arg-vals))]
          [else (error 'ZNQR "Arity mismatch.")])]
       [(closure (lamC ids body) parentEnv)
        (define argVals (map (λ ([arg : ExprC]) (interp arg env)) args))
        (cond
          [(not (= (length args) (length ids))) (error 'ZNQR "Arity mismatch")]
          [else (interp body (append (map Binding ids argVals) parentEnv))])]
       [_ (error 'ZNQR "~e not a procedure." func)])]))


;-----------------------------------------------------------------------------------------------------------------------
;; This function takes in a ZNQR Value and returns a String
(: serialize
   (Value -> String))
(define (serialize v)
  (match v
    [(? real? n) (~v n)]
    [(? boolean? p) (if p "true" "false")]
    [(prim _) "#<primop>"]
    [(? string? str) str]
    [(closure _ _) "#<procedure>"]))

;; This function calls the parser and then the desugar function and then the interp function.
(: top-interp (Sexp -> String))
(define (top-interp s)
  (serialize (interp (parse s) top-env)))


;; ----------------------------------------------------- TEST CASES ----------------------------------------------------

;; ------------------- TEST CASES FOR PARSER -------------------------

(let
    ([input 5]
     [output (numC 5)])
  (check-equal? (parse input) output))

(let
    ([input 'x]
     [output (idC 'x)])
  (check-equal? (parse input) output))

(let
    ([input "hello world! :D"]
     [output (strC "hello world! :D")])
  (check-equal? (parse input) output))

;; Test keyword as identifier
(let
    ([input 'var])
  (check-exn (regexp (regexp-quote "ZNQR: Cannot use Keyword 'var as an identifier"))
             (λ () (parse input))))


;; simple if expression
(let
    ([expr '{if true 4 5}]
     [output (ifC (idC 'true) (numC 4) (numC 5))])
  (check-equal? (parse expr) output))

;; missing else branch
(let
    ([input '{if true 4}])
  (check-exn (regexp (regexp-quote "ZNQR: if: missing an else expression.\t'(if true 4)"))
             (λ () (parse input))))

;; wrong number of branches for if
(let
    ([input '{if false 4 5 6 7 8}])
  (check-exn (regexp (regexp-quote "ZNQR: if: bad syntax.\t'(if false 4 5 6 7 8)"))
             (λ () (parse input))))

(let
    ([input '{/ 1 2}]
     [output (appC (idC '/) (list (numC 1) (numC 2)))])
  (check-equal? (parse input) output))

(let
    ([input '{f 4 3 {+ 4 5} 1}]
     [output (appC (idC 'f) (list (numC 4) (numC 3) (appC (idC '+) (list (numC 4) (numC 5))) (numC 1)))])
  (check-equal? (parse input) output))

(let
    ([input '{{x y +} -> {+ x y}}]
     [output (lamC '(x y +) (appC (idC '+) (list (idC 'x) (idC 'y))))])
  (check-equal? (parse input) output))

(let
    ([input '{{5 x} -> 5}]
    [errorMsg "ZNQR: Function parameters must be symbols.\t\'((5 x) -> 5)"])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (parse input))))
;; test var
(let
    ([input '{var {a = 1} {b = 2} {c = 4} {+ {+ a b} c}}]
     [output (appC (lamC '(a b c) (appC (idC '+) (list (appC (idC '+)
                                                             (list (idC 'a) (idC 'b))) (idC 'c))))
                   (list (numC 1) (numC 2) (numC 4)))])
  (check-equal? (parse input) output))

(let
    ([input '(var (z = (() -> 3)) (z = 9) (z))]
    [errorMsg "ZNQR: Duplicate variables."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (parse input))))

(let
    ([input '{var {-> = ""} "World"}]
    [errorMsg "ZNQR: cannot use Keyword '-> as identifier."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (parse input))))



;; test lamC
(let
    ([input '{{x x} -> 3}]
    [errorMsg "ZNQR: Duplicate variables \'(x x)"])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (parse input))))

(let
    ([input '{{var x} -> 5}]
    [errorMsg "ZNQR: cannot use Keyword 'var as identifier."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (parse input))))

;; --------------------------- TEST CASES FOR INTERPRETER ---------------------

;; ------ INTERP ----

;; Simple program -> number
(let
    ([expr (numC 3)]
     [env empty]
     [output 3])
  (check-equal? (interp expr env) output))

(let
    ([expr (numC 3)]
     [env empty]
     [output 3])
  (check-equal? (interp expr env) output))


;; Simple program -> identifer in environment
(let
    ([expr (idC 'x)]
     [env (list (Binding 'f 3) (Binding 'x 4) (Binding 'w 8))]
     [output 4])
  (check-equal? (interp expr env) output))

;; Simple program -> identifier not in environment
(let
    ([expr (idC 'x)]
     [env (list (Binding 'f 3) (Binding 't 4) (Binding 'w 8))]
     [errorMsg "ZNQR: id 'x not found."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (interp expr env))))

;; Simple program -> string
(let
    ([input (strC "hello world! :D")]
     [output "hello world! :D"])
  (check-equal? (interp input empty) output))

(let
    ([input (ifC (idC 'true) (numC 3) (numC 4))]
    [output 3])
  (check-equal? (interp input top-env) output))

(let
    ([input (ifC (idC 'false) (numC 3) (numC 4))]
    [output 4])
  (check-equal? (interp input top-env) output))

(let
    ([input (ifC (numC 3) (numC 4) (numC 5))]
    [errorMsg "ZNQR: if guard should evaluate to a boolean!"])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (interp input top-env))))

(let
    ([input (lamC '(x y) (numC 5))]
     [env top-env]
     [output (closure (lamC '(x y) (numC 5)) top-env)])
  (check-equal? (interp input env) output))

;; ----------------------- TEST CASES FOR SERIALIZE ---------------------------------
(let
    ([input 5]
     [output "5"])
  (check-equal? (serialize input) output))

(let
    ([input "hello world! :D"]
     [output "hello world! :D"])
  (check-equal? (serialize input) output))

(let
    ([input #t]
     [output "true"])
  (check-equal? (serialize input) output))

(let
    ([input #f]
     [output "false"])
  (check-equal? (serialize input) output))

(let
    ([input (prim (λ ([a : Value] [b : Value]) 5))]
     [output "#<primop>"])

  (check-equal? ((prim-func input) 3 4) 5)
  (check-equal? (serialize input) output))

(let
    ([input (closure (lamC '(a b) (numC 5)) top-env)]
     [output "#<procedure>"])
  (check-equal? (serialize input) output))

;; --- TOP-INTERP ---
(let
    ([input 5]
     [output "5"])
  (check-equal? (top-interp input) output))

(let
    ([input '{+ 3 4}]
     [output "7"])
  (check-equal? (top-interp input) output))

(let
    ([input '{+ 4 +}]
     [errorMsg "ZNQR: Expected two reals for + operator. Given\t\"4\" \"#<primop>\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{+ + 4}]
     [errorMsg "ZNQR: Expected two reals for + operator. Given\t\"#<primop>\" \"4\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{- 1 1}]
     [output "0"])
  (check-equal? (top-interp input) output))

(let
    ([input '{- 4 +}]
     [errorMsg "ZNQR: Expected two reals for - operator. Given\t\"4\" \"#<primop>\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{- + 4}]
     [errorMsg "ZNQR: Expected two reals for - operator. Given\t\"#<primop>\" \"4\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{* 2 3}]
     [output "6"])
  (check-equal? (top-interp input) output))

(let
    ([input '{* 4 +}]
     [errorMsg "ZNQR: Expected two reals for * operator. Given\t\"4\" \"#<primop>\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{* + 4}]
     [errorMsg "ZNQR: Expected two reals for * operator. Given\t\"#<primop>\" \"4\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{/ 1 2}]
     [output "1/2"])
  (check-equal? (top-interp input) output))

(let
    ([input '{/ 4 +}]
     [errorMsg "ZNQR: Expected two reals for / operator. Given\t\"4\" \"#<primop>\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{/ + 4}]
     [errorMsg "ZNQR: Expected two reals for / operator. Given\t\"#<primop>\" \"4\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{/ 4 0}]
     [errorMsg "ZNQR: Divide by 0 exception."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{<= 3 5}]
     [output "true"])
  (check-equal? (top-interp input) output))

(let
    ([input '{<= 5 3}]
     [output "false"])
  (check-equal? (top-interp input) output))

(let
    ([input '{<= true 3}]
     [errorMsg "ZNQR: Expected two reals for <= operator. Given\t\"true\" \"3\""])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{equal? 3 5}]
     [output "false"])
  (check-equal? (top-interp input) output))

(let
    ([input '{equal? 5 5}]
     [output "true"])
  (check-equal? (top-interp input) output))

(let
    ([input '{+ 1 2 3}]
     [errorMsg "ZNQR: Arity mismatch."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

(let
    ([input '{5 3}]
     [errorMsg "ZNQR: 5 not a procedure."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))


(let
    ([input '{if {<= 3 4} {+ 10 17} {- 3 3}}]
     [output "27"])
  (check-equal? (top-interp input) output))

;; test closures
(let
    ([input '{{{x y} -> {+ x y}} 1 2}]
     [output "3"])
  (check-equal? (top-interp input) output))


(let
    ([input '{{{x y} -> {+ x y}} 1 2 3}]
     [errorMsg "ZNQR: Arity mismatch"])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

;; test vars
(let
    ([input '{var {a = 1} {b = 2} {c = 4} {+ a {+ b c}}}]
     [output "7"])
  (check-equal? (top-interp input) output))

(let
    ([input '{var {a = 1} {b = 2} {c = 4}}]
     [errorMsg "ZNQR: Missing var body.\t'(var (a = 1) (b = 2) (c = 4))"])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))


(let
    ([input '{var {a = 1} {b = 2} {88 = 4} {+ a {+ b c}}}]
     [errorMsg "ZNQR: variable ids must be symbols."])
  (check-exn (regexp (regexp-quote errorMsg))
             (λ () (top-interp input))))

;; Tests failing
;; (top-interp '{var {f = {{x} -> y}} {var {y = 9} {f 3}}})


