#lang typed/racket
(require typed/rackunit)

;;> eyeball: 4/6, a number of medium-sized errors, see comments below.


;;;;;;;;;;;;;;;;;;;;;;;;;;;Assignment 3;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;> thanks for the comment. These are parse tests, I'm guessing you've fixed them by now.

;Currently failing final 3 tests. Unsure exact reason beacuse honestly they're
;alot to try and read and understand 

;;Definitons for Expressions
(define-type ExprC ( U NumC StringC IfC IdC AppC LamC))
(struct NumC  ([n : Real]) #:transparent)
(struct StringC ([str : String]) #:transparent)
(struct IfC ([my_if : ExprC] [my_then : ExprC] [my_else : ExprC]) #:transparent)
(struct IdC ([s : Symbol] ) #:transparent)
(struct AppC ([func : ExprC] [arg : (Listof ExprC)]) #:transparent)
(struct LamC ([params : (Listof IdC)] [body : ExprC]) #:transparent)

;Deffinition for Sugared Function (Functions with variables)
(define-type ExprS ( U LamS ))
(struct LamS ([varibles : (Listof Any)][body : ExprC]) #:transparent)

;;Definition for Values
(define-type Value (U NumV StringV CloV PrimV BoolV))
(struct NumV ([n : Real]) #:transparent)
(struct CloV ([param : (Listof IdC)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV ([sym : Symbol]) #:transparent)
(struct StringV ([s : String]) #:transparent)
(struct BoolV ([bool : Boolean]) #:transparent)


;;Definiton for Environments
(define-type Env (Immutable-HashTable Symbol Value))

;;Top Level Environment
(define top-level-hash (make-immutable-hash
    (list
     (cons `+ (PrimV '+))
     (cons `- (PrimV '-))
     (cons `* (PrimV '*))
     (cons `/ (PrimV '/))
     (cons `<= (PrimV '<=))
     (cons `equal? (PrimV 'equal?))
     (cons `true (BoolV true))
     (cons `false (BoolV false))
)))

;Hash Map used for binop operations
(define binop_hash_map (make-immutable-hash
    (list (cons `+ +)
          (cons `* *)
          (cons `- -)
          (cons `/ /)
)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Parse;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Given a list from a 'var extracts parameters into list of IdCs
(define (get_params [l : (Listof Any)]) : (Listof IdC)
       (cond [(empty? l) l]
        [else
         (match (first l)
           ;;> this needs a catch-all case (or just check it in the
           ;;> parser). This is a bug.
           [(list (? symbol? param) '= arg)
            (cons (IdC param) (get_params (rest l)))])]
        ;;> pull all these trailing parens up, per the style guide
     )
  )

;Given a list from a 'var extracts arguments into list of ExprC
(define (get_args [l : (Listof Any)]) : (Listof ExprC)
       (cond [(empty? l) l]
        [else
         (match (first l)
           [(list (? symbol? param) '= arg)
            (cons (parse (cast arg Sexp)) (get_args (rest l)))])]
     )
  )

;Given a function with variables listed this desugars into ExprC type
(define (desugar [s : ExprS]) : ExprC
  (match s
      [(LamS variables body)
       (define params (get_params variables))
       (cond [(check-duplicates params) (error "ZNQR: Duplicate Parameters in var")])
       (define args (get_args variables))
       (AppC (LamC params body) args)]
   )
)

;Takes syntax for ZNQR3 language as s-expression and parses into ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
      ;Number
      [(? real? n) (NumC n)]
      ;String
      [(? string? s) (StringC s)]
      ;If
      [(list `if args ... )
             (if ( = (length args) 3)
                 (IfC (parse (first args)) (parse (second args)) (parse (third args)))
                 (error "ZNQR: parse Bad Input"))]
      ;Var (Desugar)
      [(list 'var variable ... body) (desugar (LamS variable (parse body)))]
      ;LamC (Function)
      [(list (list (? symbol? params) ... ) '-> body)
                    (define param_list ((inst map IdC Symbol) (λ (a) (IdC a)) (cast params (Listof Symbol))))
                    (if (check-duplicates param_list)
                        (error "ZNQR: Duplicate Parameters")
                        (LamC param_list (parse body)))]
      ;AppC
      [(list func args ... )(define func_call (parse func))
                            (cond [(NumC? func_call) (error "ZNQR: parse Bad Input")])
                            (if (hash-has-key? top-level-hash func)
                                  (if (= (length args)2)
                                       (AppC func_call (map parse args))
                                       (error "ZNQR: parse Bad Input"))
                                  (AppC func_call (map parse args)))]
      ;IdC
      [(? symbol? sym )
           (if (not (or (eq? sym `if) (eq? sym `var) (eq? sym `->) (eq? sym `==)))
                (IdC sym)
                (error "ZNQR: parse Bad Input"))]
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;Serialize;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Given a Value type returns as a String
(define (serialize [val : Value]) : String
   (match val
     [(NumV n) (~v n)]
     [(CloV p d e) "#<procedure>"]
     [(PrimV s)  "#<primop>"]
     [(StringV s) (~v s)]
     [(BoolV b)
        (match b
            [#t "true"]
            [#f "false"])])
)


;;;;;;;;;;;;;;;;;;;Interp Expression given List of Functions;;;;;;;;;;;;;;;;;;;;;;;;;;

;Given symbol and enviorment returns assosiated Value or error if not found
(define (id-look-up [sym : Symbol]  [env : Env]) : Value
    (hash-ref env sym (λ () (error "ZNQR Id not found: ~e" sym)))
)

;Adds list of Symbol andits respective list of Values to given enviroment
(define (extend-env [env : Env] [syms : (Listof Symbol)] [values : (Listof Value)]) : Env
     (cond [(empty? syms) env]
        [else (extend-env (hash-set env (first syms) (first values)) (rest syms) (rest values))
        ]
     )
)

;given a operativer and list of values preforms the appropriate operation and returns Value
(define (prim-handler [op : Symbol] [args : (Listof Value)]) : Value
   (if (not (= (length args) 2))
       (error "ZNQR Incorrect number of arguments")
        (match op
           ['equal? (BoolV (equal? (first args) (second args)))]
           [_ (match (first args)
                 [(NumV n1) (match (second args)
                              [(NumV n2)
                               (cond [(and (eq? '/ op) (= 0 n2))
                                       (error "ZNQR: divide by zero")])
                               (if (hash-has-key? binop_hash_map op)
                                             (NumV ((hash-ref binop_hash_map op) n1 n2))
                                             (BoolV (<= n1 n2)))]
                              [_ (error "ZNQR Second argument not a real number")])]
                [_ (error "ZNQR First argument not a real number")])])))


;;> move interp up to make this top-down per the syllabus

;Takes an ExprC and environment in order to caculate the a Value
(define (interp  [exp : ExprC]  [env : Env] ) : Value
   (match exp
    [(NumC n) (NumV n)]
    [(IdC x) (id-look-up x env)]
    [(StringC s) (StringV s)]
    [(IfC my_if my_then my_else)
     ;;> double-interp will lead to exponential behavior in some cases
      (if (BoolV? (interp my_if env))
          (if  (equal? (BoolV true) (interp my_if env))
               (interp my_then env)
               (interp my_else env))
          (error "ZNQR If test did not evaluate to a boolean"))]
    [(LamC params body) (CloV params body env)]
    [(AppC func args)
     ;;> this code fails to catch arity errors. see example at bottom
      (cond [(LamC? func)
            (cond [(not (= (length (LamC-params func)) (length args)))
                  (error "ZNQR Incorrect Number Of Arguments")])])
      (define argvals (map (λ ([x : ExprC]) (interp x env)) args))
      (match (interp func env)
        [(PrimV op) (prim-handler op argvals)]
        [(CloV params body cloenv)
           (define new-env  (extend-env cloenv (map (λ ([x : IdC]) (IdC-s x)) params) argvals))
           (interp body new-env)
        ]
        [_ (error "ZNQR Bad Input")])]
    )
 )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Top Interp;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Parses program and evaluates. Returns evaluated value as string
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-level-hash)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Tests;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Tests for Top Interp
(check-equal? (top-interp '{<= 2 1}) "false" )
(check-equal? (top-interp '{if {<= 1 2} {+ 1 2} 0}) "3")
(check-equal? (top-interp '{{{x} -> 1} 3} ) "1")
(check-equal? (top-interp '{{{x y} -> {+ 1 y}} {+ 1 2} {* 7 3}}) "22")
(check-exn  exn:fail? (lambda () (top-interp '{{{} -> 9} 17}))
             "ZNQR Incorrect Number Of arguments")
(check-exn  exn:fail? (lambda () (top-interp '{/ 1 {- 3 3}} ))
              "ZNQR: divide by zero")
(check-exn  exn:fail? (lambda () (top-interp '{{{{} -> 3}} 4 5 }))
              "ZNQR Bad Input")

;Tests for Parse
(check-equal? (parse '{var {z = {+ 9 14}} {y = 98} {+ z y}})
              (AppC (LamC (list (IdC 'z) (IdC 'y)) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                  (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-equal? (parse 1) (NumC 1))
(check-equal? (parse "hi") (StringC "hi"))
(check-equal? (parse '{<= 2 1}) (AppC (IdC '<=) (list (NumC 2) (NumC 1))))
(check-equal? (parse '{if {<= 2 1} {+ 1 2} 0})
              (IfC (AppC (IdC '<=) (list (NumC 2) (NumC 1)))
                   (AppC (IdC '+) (list (NumC 1) (NumC 2))) (NumC 0)))
(check-equal? (parse '{{x} -> 1}) (LamC (list (IdC 'x)) (NumC 1)))
(check-equal? (parse '{{x y} -> {+ 1 y}}) (LamC (list (IdC 'x) (IdC 'y)) (AppC (IdC '+) (list (NumC 1) (IdC 'y)))))
(check-equal? (parse '{{{x y} -> {+ 1 y}} 4 5 }) (AppC
                                    (LamC (list (IdC 'x) (IdC 'y)) (AppC (IdC '+) (list (NumC 1) (IdC 'y))))
                                    (list (NumC 4) (NumC 5))))
(check-exn  exn:fail? (lambda () (parse '{+ 5})) "ZNQR: parse Bad Input" )
(check-exn  exn:fail? (lambda () (parse 'if)) "ZNQR: parse Bad Input" )
(check-exn  exn:fail? (lambda () (parse '{if})) "ZNQR: parse Bad Input" )
(check-exn  exn:fail? (lambda () (parse '{+ if a})) "ZNQR: parse Bad Input" )
(check-exn  exn:fail? (lambda () (parse 'var)) "ZNQR: parse Bad Input" )
(check-exn  exn:fail? (lambda () (parse '{3 4 5})) "ZNQR: parse Bad Input" )
(check-exn  exn:fail? (lambda () (parse '{{x x} -> 3})) "ZNQR: Duplicate Parameters" )
(check-exn  exn:fail? (lambda () (parse '{var {z = {{} -> 3}} {z = 9} {z}})) "ZNQR: Duplicate Parameters in var")

;Tests for Serialize
(check-equal? (serialize (NumV 2)) "2")
(check-equal? (serialize (StringV "hi")) "\"hi\"")
(check-equal? (serialize (BoolV true)) "true")
(check-equal? (serialize (BoolV false)) "false")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (CloV (list (IdC 'x)) (AppC (IdC '+) (list (NumC 2) (NumC 1))) top-level-hash))
              "#<procedure>")

;Tests for Interp
(check-equal? (interp (NumC 2) top-level-hash) (NumV 2))
(check-equal? (interp (StringC "Hi") top-level-hash) (StringV "Hi"))
(check-equal? (interp (IdC '+) top-level-hash) (PrimV '+))
(check-equal? (interp (AppC (IdC '+) (list (NumC 2) (NumC 1))) top-level-hash) (NumV 3))
(check-equal? (interp (AppC (IdC '-) (list (NumC 2) (NumC 1))) top-level-hash) (NumV 1))
(check-equal? (interp (AppC (IdC '*) (list (NumC 2) (NumC 1))) top-level-hash) (NumV 2))
(check-equal? (interp (AppC (IdC '/) (list (NumC 12) (NumC 3))) top-level-hash) (NumV 4))
(check-equal? (interp (AppC (IdC '<=) (list (NumC 2) (NumC 1))) top-level-hash) (BoolV false))
(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 2) (NumC 2))) top-level-hash) (BoolV true))
(check-equal? (interp (LamC (list (IdC 'x)) (AppC (IdC '+) (list (NumC 2) (NumC 1)))) top-level-hash)
                      (CloV (list (IdC 'x)) (AppC (IdC '+) (list (NumC 2) (NumC 1))) top-level-hash))
(check-equal? (interp (AppC
                       (LamC (list (IdC 'x)) (AppC (IdC '+) (list (NumC 2) (NumC 1))))
                       (list (NumC 2)))
                       top-level-hash)
                       (NumV 3))
(check-equal? (interp (AppC
                       (LamC (list (IdC 'x)) (AppC (IdC '+) (list (IdC 'x) (NumC 1))))
                       (list (NumC 2)))
                       top-level-hash)
                       (NumV 3))
(check-equal? (interp (AppC
                       (LamC (list (IdC 'x) (IdC 'y)) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                       (list (NumC 2) (NumC 2)))
                       top-level-hash)
                       (NumV 4))
(define appcmult  (AppC (LamC (list (IdC 'x) (IdC 'y)) (AppC (IdC '*) (list (IdC 'x) (IdC 'y))))
                       (list (NumC 3) (NumC 4))))
(define lamcadd (LamC (list (IdC 'x) (IdC 'y)) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))))
(check-equal? (interp (AppC lamcadd (list appcmult (NumC 2))) top-level-hash)
                       (NumV 14))
(define false-test (AppC (IdC 'equal?) (list (NumC 0) (NumC 1))))
(check-equal? (interp false-test top-level-hash) (BoolV false))
(define true-test (AppC (IdC 'equal?) (list (NumC 0) (NumC 0))))
(check-equal? (interp true-test top-level-hash) (BoolV true))
(check-equal? (interp (IfC true-test
                           (AppC lamcadd (list appcmult (NumC 2)))
                           (NumC 0))
                      top-level-hash) (NumV 14))
(check-equal? (interp (IfC false-test
                           appcmult
                           (NumC 0))
                      top-level-hash) (NumV 0))
(check-exn  exn:fail? (lambda () (interp (IdC 'idc) top-level-hash))
             "ZNQR Id not found: idc")
(check-exn  exn:fail? (lambda () (interp (AppC (IdC '+) (list (NumC 2) (NumC 1) (NumC 0))) top-level-hash))
             "ZNQR Incorrect number of arguments")
(check-exn  exn:fail? (lambda () (interp (AppC (IdC '+) (list (NumC 2) (NumC 1) (NumC 0))) top-level-hash))
             "ZNQR Incorrect number of arguments")
(check-exn  exn:fail? (lambda () (interp (AppC (IdC '+) (list (IdC '+) (NumC 1))) top-level-hash))
             "ZNQR First argument not a real number")
(check-exn  exn:fail? (lambda () (interp (AppC (IdC '+) (list (NumC 2) (IdC '+))) top-level-hash))
             "ZNQR Second argument not a real number")
(check-exn  exn:fail? (lambda () (interp (AppC (IdC '+) (list (NumC 2) (IdC '+))) top-level-hash))
             "ZNQR Second argument not a real number")
(check-exn  exn:fail? (lambda () (interp (IfC (NumC 5)
                                         (AppC lamcadd (list appcmult (NumC 2)))
                                         (NumC 0))
                                         top-level-hash))
                                          "ZNQR If test did not evaluate to a boolean")

(top-interp '{var {f = {{} -> 13}}
                  {f 9}})
(parse '{var {a 13} a})