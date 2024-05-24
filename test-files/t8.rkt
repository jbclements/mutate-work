#lang typed/racket

(require typed/rackunit)


;;; FULL PROJECT IMPLEMENTED



;; DEFINITIONS

; JYSS Expression type union
(define-type ExprC (U NumC IdC StrC IfC LamC AppC RecC))

; JYSS Expression struct definitions
(struct NumC ([n : Real]) #:transparent)
(struct IdC ([s : Symbol]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IfC ([cond : ExprC] [t : ExprC] [f : ExprC]) #:transparent)
(struct LamC ([args : (Listof TypedSymbol)] [body : ExprC]) #:transparent)
(struct AppC ([args : (Listof ExprC)] [body : ExprC]) #:transparent)
(struct RecC ([s : Symbol] [args : (Listof TypedSymbol)] [t : Type] [body : ExprC] [expr : ExprC]) #:transparent)

; JYSS Value type union
(define-type Value (U NumV BoolV ClosV PrimopV StrV))

; JYSS Value struct definitions
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct ClosV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimopV ([op : ((Listof Value) -> Value)]) #:transparent)
(struct StrV ([str : String]) #:transparent)

; JYSS Environment definitions
(define-type Env (Listof Binding))
(struct Binding ([name : Symbol] [value : (Boxof Value)]) #:transparent)

; JYSS Types
(define-type Type (U 'NumT 'BoolT 'StrT FunT))
(struct FunT ([args : (Listof Type)] [ret : Type]) #:transparent)

; JYSS Type Environments
(define-type TypeEnv (Listof TypedSymbol))

; Additional structs
(struct TypedSymbol ([s : Symbol] [t : Type]) #:transparent)



;; TOP LEVEL FUNCTIONS

; Parses and interprets a JYSS program
(define (top-interp [s : Sexp]) : String
  (define parsed-program (parse s))
  (type-check parsed-program base-tenv)
  (serialize (interp parsed-program (top-env))))

; Parses an s-expression into a single JYSS expression
(define (parse [s : Sexp]) : ExprC
  (match s
    ; Main ExprCs
    [(? real? num) (NumC num)]
    [(? string? str) (StrC str)]
    [(? unreserved-symbol? id) (IdC id)]
    ; Desugaring
    [(list 'vars: (list (? unreserved-symbol? l) ': types '= r) ... 'body: body)
     (if (check-duplicates l)
         (error 'parse "[JYSS] Duplicate arguments: ~e" l)
         (AppC (map parse (cast r (Listof Sexp)))
               (LamC (map (λ (s t) (TypedSymbol s t))
                          (cast l (Listof Symbol))
                          (cast (map parse-type (cast types (Listof Sexp))) (Listof Type))) (parse body))))]
    ; Recursive
    [(list 'rec: (list (? unreserved-symbol? id) '=
                       (list 'proc (list (list (? unreserved-symbol? args) ': types) ...) ': type 'go body)) 'in expr)
     (if (check-duplicates args)
         (error 'parse "[JYSS] Duplicate arguments: ~e" args)
         (RecC id
               (map (λ (s t) (TypedSymbol s t))
                    (cast args (Listof Symbol))
                    (cast (map parse-type (cast types (Listof Sexp))) (Listof Type)))
               (parse-type type)
               (parse body)
               (parse expr)))]
    ; Other list-based ExprCs
    [(list 'if cond true false) (IfC (parse cond) (parse true) (parse false))]
    [(list 'proc (list (list (? unreserved-symbol? args) ': types) ...) 'go body)
     (if (check-duplicates args)
         (error 'parse "[JYSS] Duplicate arguments: ~e" args)
         (LamC (map (λ (s t) (TypedSymbol s t)) (cast args (Listof Symbol))
                    (map parse-type (cast types (Listof Sexp))))
               (parse body)))]
    [(list fun args ...) (AppC (map parse args) (parse fun))]
    ; Errors
    [else (error 'parse "[JYSS] Invalid input: ~e" s)]))

; Interprets (evaluates) a JYSS expression
(define (interp [exp : ExprC] [env : Env]) : Value
  (match exp
    [(IdC sym) (env-lookup sym env)]
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    [(IfC cond true false) (define interped-cond (interp cond env))
                           (if (BoolV? interped-cond)
                               (if (BoolV-b interped-cond) (interp true env) (interp false env))
                               (error 'interp "[JYSS] Non-boolean condition: ~e" interped-cond))]
    [(AppC args body) (define interped-args (interp-many args env))
                      (match (interp body env)
                        [(ClosV a b e) (if (equal? (length args) (length a))
                                           (interp b (append (bind-args a interped-args) e))
                                           (error 'interp "[JYSS] Argument count mismatch: ~e provided, ~e expected"
                                                  (length args) (length a)))]
                        [(PrimopV op) (op interped-args)]
                        [else (error 'interp "[JYSS] Application of non-closure: ~e" else)])]
    [(LamC args body) (ClosV (map TypedSymbol-s args) body env)]
    [(RecC sym args type body expr) (begin (define new-env (cons (Binding sym (box (StrV "dummy"))) env))
                                           (define rec-clos (ClosV (map TypedSymbol-s args) body new-env))
                                           (update-env new-env sym rec-clos)
                                           (interp expr new-env))]))

; Type Checking
(define (type-check [exp : ExprC] [env : TypeEnv]) : Type
  (match exp
    [(IdC sym) (type-env-lookup sym env)]
    [(NumC n) 'NumT]
    [(StrC s) 'StrT]
    [(IfC cond true false) (define cond-type (type-check cond env))
                           (define true-type (type-check true env))
                           (define false-type (type-check false env))
                           (if (equal? cond-type 'BoolT)
                               (if (equal? true-type false-type)
                                   true-type
                                   (error 'type-check "[JYSS] Non-matching types in if statement: ~e and ~e"
                                          true-type false-type))
                               (error 'type-check "[JYSS] Non-boolean condition: ~e" cond-type))]
;;> You can specify the type for arg to avoid that cast.
    [(AppC args body) (define args-types (map (λ (arg) (type-check (cast arg ExprC) env)) args))
                      (match (type-check body env)
                        [(FunT in out)
                         (if (equal? args-types in) out
                             (error 'type-check "[JYSS] Argument mismatch: ~e provided, ~e expected" args-types in))]
                        [else (error 'type-check "[JYSS] Application of non-closure: ~e" else)])]
    [(LamC args body) (FunT (map TypedSymbol-t args) (type-check body (append env args)))]
    [(RecC sym args type body expr) (define dec-type (TypedSymbol sym (FunT (map TypedSymbol-t args) type)))
                                    (define act-type (type-check body (cons dec-type (append env args))))
                                    (if
                                     (equal? type act-type)
                                     (type-check expr (cons dec-type env))
                                     (error 'type-check
                                            "[JYSS] Mismatched expression types: wanted ~e, got ~e" type act-type))]))



;; HELPER METHODS

; serialize - Serializes JYSS values into Strings
(define (serialize [value : Value]) : String
  (match value
    [(NumV num) (~v num)]
    [(BoolV bool) (if bool "true" "false")]
    [(ClosV _ _ _) "#<procedure>"]
    [(PrimopV _) "#<primop>"]
    [(StrV str) (~v str)]))

; interp-many - Interprets a list of ExprCs into a list of Values
(define (interp-many [args : (Listof ExprC)] [env : Env]) : (Listof Value)
  (match args
    ['() '()]
    [(cons fst rst) (cons (interp fst env) (interp-many rst env))]))

; bind-args - Creates an environment from parallel lists of symbols and values
(define (bind-args [symbols : (Listof Symbol)] [vals : (Listof Value)]) : Env
  (match symbols
    ['() '()]
    [(cons fst rst) (cons (Binding fst (box (first vals))) (bind-args rst (rest vals)))]))

; env-lookup - Looks up a value in the environment
(define (env-lookup [sym : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'env-lookup "[JYSS] Reference to undefined value: ~e" sym)]
    [(cons? env)
     (cond
       [(equal? sym (Binding-name (first env))) (unbox (Binding-value (first env)))]
       [else (env-lookup sym (rest env))])]))

; type-env-lookup - Looks up a type in the type environment
(define (type-env-lookup [sym : Symbol] [env : TypeEnv]) : Type
  (cond
    [(empty? env) (error 'env-lookup "[JYSS] Reference to undefined type: ~e" sym)]
    [(cons? env)
     (cond
       [(equal? sym (TypedSymbol-s (first env))) (TypedSymbol-t (first env))]
       [else (type-env-lookup sym (rest env))])]))

; top-env-primop-binding - Currying/binding for top env primops
(define (top-env-primop-binding [sym : Symbol]) : Binding
  (Binding sym (box (PrimopV (lambda ([vals : (Listof Value)]) (interp-primop sym vals))))))

; top-env - Create the root environment
(define (top-env) : Env
  (list
   (top-env-primop-binding 'substring)
   (top-env-primop-binding '+)
   (top-env-primop-binding '-)
   (top-env-primop-binding '*)
   (top-env-primop-binding '/)
   (top-env-primop-binding '<=)
   (top-env-primop-binding 'num-eq?)
   (top-env-primop-binding 'str-eq?)
   (Binding 'true (box (BoolV #t)))
   (Binding 'false (box (BoolV #f)))))

; base-tenv - Define the root environment's types
;;> have you ever considered, instead of typing out (funT ......) yourself,
;;> you can just (TypedSymbol '+ (parse-type '(num num -> num)))
;;> you already have the parse-type function, use it to your advantage.
(define base-tenv
  (list
   (TypedSymbol 'substring (FunT '(StrT NumT NumT) 'StrT))
   (TypedSymbol '+ (FunT '(NumT NumT) 'NumT))
   (TypedSymbol '- (FunT '(NumT NumT) 'NumT))
   (TypedSymbol '* (FunT '(NumT NumT) 'NumT))
   (TypedSymbol '/ (FunT '(NumT NumT) 'NumT))
   (TypedSymbol '<= (FunT '(NumT NumT) 'BoolT))
   (TypedSymbol 'num-eq? (FunT '(NumT NumT) 'BoolT))
   (TypedSymbol 'str-eq? (FunT '(StrT StrT) 'BoolT))
   (TypedSymbol 'true 'BoolT)
   (TypedSymbol 'false 'BoolT)))

; update-env - Replaces a value in the environment (mutation)
(define (update-env [e : Env] [s : Symbol] [v : Value]) : Void
  (match e
    ['() (error 'update-env "[JYSS] Cannot update undefined binding: ~e" s)]
    [(cons (Binding sym val) rst) (if (equal? sym s)
                                      (set-box! val v)
                                      (update-env rst s v))]))

; interp-primop - Has all the primop functionality
(define (interp-primop [op : Symbol] [args : (Listof Value)]) : Value
  (cond
    [(equal? op 'substring) (match args
                              [(list (StrV s) (NumV n1) (NumV n2))
                               ;;> you forgot to check cases where index = 0.5
                               ;;> bugs. see test cases on the bottom
                               (if (or (< n1 0) (< (string-length s) (+ n2 1)) (> n1 n2))
                                   (error 'interp-primop "[JYSS] Improper bounds on substring: start ~e, end ~e" n1 n2)
                                   (StrV (substring s (exact-floor n1) (exact-floor n2))))]
                              [else (error 'interp-primop "[JYSS] Incorrect arguments to substring: ~e" args)])]
    [(not (equal? (length args) 2))
     (error 'interp-primop "[JYSS] Incorrect number of arguments on primitive operator: ~e" op)]
    [else (define l (first args))
          (define r (second args))
          (cond
            [(equal? op 'str-eq?) (BoolV (equal? l r))]
            [(or (not (NumV? l)) (not (NumV? r)))
             (error 'interp-primop "[JYSS] Nonnumeric value(s) passed to arithmetic binary operator: ~e and ~e" l r)]
            [(equal? op 'num-eq?) (BoolV (equal? l r))]
            [(equal? op '+) (NumV (+ (NumV-n l) (NumV-n r)))]
            [(equal? op '-) (NumV (- (NumV-n l) (NumV-n r)))]
            [(equal? op '*) (NumV (* (NumV-n l) (NumV-n r)))]
            [(equal? op '/) (if (equal? (NumV-n r) 0)
                                (error 'interp-primop "[JYSS] Division by zero")
                                (NumV (/ (NumV-n l) (NumV-n r))))]
            [(equal? op '<=) (BoolV (<= (NumV-n l) (NumV-n r)))]
            [else (error 'interp-primop "[JYSS] Invalid primop: ~e" op)])]))

; unreserved-symbol - Checks that a symbol is not a reserved symbol for other expressions
;;> oops, missing some keywords, unfortunately. see failed test cases on the bottom
(: unreserved-symbol? (Any -> Boolean : #:+ Symbol))
(define (unreserved-symbol? s)
  (match s
    ['vars: #f]
    ['body: #f]
    ['rec: #f]
    ['if #f]
    ['proc #f]
    ['go #f]
    [(? symbol? s) #t]
    [else #f]))

; parse-type - parses the user-supplied types into a Type
(define (parse-type [s : Sexp]) : Type
  (match s
    ['num 'NumT]
    ['bool 'BoolT]
    ['str 'StrT]
    [(list inputs ... '-> output) (FunT (map parse-type (cast inputs (Listof Sexp))) (parse-type output))]
    [else (error 'parse-type "[JYSS] Unrecognized type: ~e" else)]))



;; TEST CASES
(define EPSILON 0.001)

; top-interp - full JYSS programs :)
(check-equal? (top-interp '5) "5")
(check-equal? (top-interp '{+ 1 2}) "3")
(check-equal? (top-interp 'true) "true")
(check-equal? (top-interp '{num-eq? {+ 4 8} {* 3 4}}) "true")
(check-equal? (top-interp '{proc {[x : num] [y : num] [z : num]} go {+ x {* y z}}}) "#<procedure>")
(check-equal? (top-interp
               '{vars:
                 [add : {{{num -> num} -> {num -> num}}
                         -> {{{num -> num} -> {num -> num}}
                             -> {{num -> num} -> {num -> num}}}} = {proc
                                                                    {[n1 : {{num -> num} -> {num -> num}}]}
                                                                    go
                                                                    {proc
                                                                     {[n2 : {{num -> num} -> {num -> num}}]}
                                                                     go
                                                                     {proc {[f : {num -> num}]}
                                                                           go {proc
                                                                               {[a : num]} go {{n2 f} {{n1 f} a}}}}}}]
                 [one : {{num -> num} -> {num -> num}} = {proc {[f : {num -> num}]} go {proc {[a : num]} go {f a}}}]
                 [two : {{num -> num} -> {num -> num}} = {proc {[f : {num -> num}]} go {proc {[a : num]} go {f {f a}}}}]
                 [double : {num -> num} = {proc {[x : num]} go {* 2 x}}]
                 body: {num-eq? {{{{add one} two} double} 1} 8}}) "true")
(check-equal? (top-interp '{rec: [f = {proc {[x : num]} : num go {if {<= x 1} x {f {/ x 2}}}}] in {f 16}}) "1")
(check-equal? (top-interp
               '{rec:
                 [square-helper = {proc {[n : num]} : num go {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}]
                 in {vars:
                     [square : {num -> num} = {proc {[n : num]} go {square-helper {- {* 2 n} 1}}}]
                     body: {square 13}}}) "169")

; parse
(check-equal? (parse 1) (NumC 1))
(check-equal? (parse 'x) (IdC 'x))
(check-equal? (parse "woohoo") (StrC "woohoo"))
(check-equal? (parse '(if true 7 true)) (IfC (IdC 'true) (NumC 7) (IdC 'true)))
(check-equal? (parse '(proc ([x : num]) go x)) (LamC (list (TypedSymbol 'x 'NumT)) (IdC 'x)))
(check-equal? (parse '(f x y z)) (AppC (list (IdC 'x) (IdC 'y) (IdC 'z)) (IdC 'f)))
(check-exn (regexp (regexp-quote "[JYSS] Invalid input: 'go")) (λ () (parse '(proc ([proc : num] [go : num]) go go))))
(check-exn (regexp (regexp-quote "[JYSS] Invalid input: 'if")) (λ () (parse '(if true cry))))
(check-exn (regexp (regexp-quote "[JYSS] Duplicate arguments: '(hello hello)"))
           (λ () (parse '(proc ([hello : bool] [hello : str]) go 1))))
(check-equal? (parse '{vars: [x : num = 1] [y : num = 2] body: {+ x y}})
              (AppC (list (NumC 1) (NumC 2)) (LamC (list (TypedSymbol 'x 'NumT) (TypedSymbol 'y 'NumT))
                                                   (AppC (list (IdC 'x) (IdC 'y)) (IdC '+)))))
(check-exn (regexp (regexp-quote "[JYSS] Duplicate arguments: '(x x)"))
           (λ () (parse '{vars: [x : num = 1] [x : num = 2] body: {+ x x}})))
(check-equal? (parse '{rec: [f = {proc {[x : num]} : num go {if {<= 1 x} x {f {/ x 2}}}}] in {f 16}})
              (RecC 'f (list (TypedSymbol 'x 'NumT)) 'NumT
                    (IfC (AppC (list (NumC 1) (IdC 'x)) (IdC '<=))
                         (IdC 'x)
                         (AppC (list (AppC (list (IdC 'x) (NumC 2)) (IdC '/))) (IdC 'f)))
                    (AppC (list (NumC 16)) (IdC 'f))))
(check-exn (regexp (regexp-quote "[JYSS] Duplicate arguments: '(x x)"))
           (λ () (parse '{rec: [f = {proc {[x : num] [x : num]} : num go {if {<= 1 x} x {f {/ x 2}}}}] in {f 16}})))

; interp
(check-equal? (interp (NumC 7) '()) (NumV 7))
(check-equal? (interp (StrC "oh yeah") '()) (StrV "oh yeah"))
(check-equal? (interp (IdC 'x) (list (Binding 'x (box (NumV 8))))) (NumV 8))
(check-equal? (interp (IfC (IdC 'true) (NumC 7) (IdC 'true)) (top-env)) (NumV 7))
(check-equal? (interp (IfC (IdC 'false) (NumC 7) (IdC 'true)) (top-env)) (BoolV #t))
(check-exn (regexp (regexp-quote "[JYSS] Non-boolean condition: (NumV 7)"))
           (λ () (interp (IfC (NumC 7) (NumC 7) (IdC 'true)) (top-env))))
(check-exn (regexp (regexp-quote "[JYSS] Application of non-closure: (NumV 1)"))
           (λ () (interp (AppC '() (NumC 1)) (top-env))))
(check-equal? (interp (AppC (list (NumC 5) (NumC 2)) (IdC '+)) (top-env)) (NumV 7))
(check-equal? (interp (AppC (list (NumC 5)) (LamC (list (TypedSymbol 'x 'NumT))
                                                  (AppC (list (IdC 'x) (IdC 'x)) (IdC '*)))) (top-env)) (NumV 25))
(check-exn (regexp (regexp-quote "[JYSS] Argument count mismatch: 2 provided, 1 expected"))
           (λ () (interp (AppC (list (NumC 5) (NumC 2)) (LamC (list (TypedSymbol 'x 'NumT))
                                                              (AppC (list (IdC 'x) (IdC 'x)) (IdC '*)))) (top-env))))
(check-exn (regexp (regexp-quote "[JYSS] Argument count mismatch: 1 provided, 2 expected"))
           (λ () (interp (AppC (list (NumC 5)) (LamC (list (TypedSymbol 'x 'NumT) (TypedSymbol 'y 'NumT))
                                                     (AppC (list (IdC 'x) (IdC 'y)) (IdC '*)))) (top-env))))
(check-equal? (interp (RecC 'f (list (TypedSymbol 'x 'NumT)) 'NumT
                            (IfC (AppC (list (IdC 'x) (NumC 1)) (IdC '<=)) (IdC 'x)
                                 (AppC (list (AppC (list (IdC 'x) (NumC 2)) (IdC '/))) (IdC 'f)))
                            (AppC (list (NumC 16)) (IdC 'f))) (top-env)) (NumV 1))

; type-check
(check-equal? (type-check (NumC 8) base-tenv) 'NumT)
(check-equal? (type-check (StrC "foo") base-tenv) 'StrT)
(check-equal? (type-check (IdC '+) base-tenv) (FunT '(NumT NumT) 'NumT))
(check-equal? (type-check (IdC '<=) base-tenv) (FunT '(NumT NumT) 'BoolT))
(check-equal? (type-check (IdC 'str-eq?) base-tenv) (FunT '(StrT StrT) 'BoolT))
(check-equal? (type-check (IfC (IdC 'true) (NumC 7) (NumC 0)) base-tenv) 'NumT)
(check-equal? (type-check (LamC (list (TypedSymbol 'x 'NumT) (TypedSymbol 'y 'StrT) (TypedSymbol 'z 'BoolT))
                                (IdC 'y)) base-tenv) (FunT '(NumT StrT BoolT) 'StrT))
(check-equal? (type-check (AppC (list (NumC 0) (NumC 2)) (IdC '+)) base-tenv) 'NumT)
(check-equal? (type-check (LamC (list (TypedSymbol 'x 'NumT) (TypedSymbol 'y 'BoolT))
                                (IfC (IdC 'y) (IdC 'x) (NumC 1))) base-tenv) (FunT '(NumT BoolT) 'NumT))
(check-exn (regexp (regexp-quote "[JYSS] Non-boolean condition: 'StrT"))
           (λ () (type-check (IfC (StrC "ohno") (NumC 2) (NumC 3)) base-tenv)))
(check-exn (regexp (regexp-quote "[JYSS] Non-matching types in if statement: 'NumT and 'StrT"))
           (λ () (type-check (IfC (IdC 'true) (NumC 2) (StrC "ohno")) base-tenv)))
(check-exn (regexp (regexp-quote "[JYSS] Application of non-closure: 'StrT"))
           (λ () (type-check (AppC '() (StrC "ohno")) base-tenv)))
(check-exn (regexp (regexp-quote "[JYSS] Argument mismatch: '(NumT StrT) provided, '(NumT NumT) expected"))
           (λ () (type-check (AppC (list (NumC 12) (StrC "oops")) (IdC '+)) base-tenv)))
(check-equal? (type-check (RecC 'f (list (TypedSymbol 'x 'NumT)) 'NumT
                                (IfC (AppC (list (NumC 1) (IdC 'x)) (IdC '<=))
                                     (IdC 'x)
                                     (AppC (list (AppC (list (IdC 'x) (NumC 2)) (IdC '/))) (IdC 'f)))
                                (AppC (list (NumC 16)) (IdC 'f))) base-tenv) 'NumT)
(check-exn (regexp (regexp-quote "[JYSS] Mismatched expression types: wanted 'NumT, got 'StrT"))
           (λ () (type-check (parse '(rec: (a = (proc ((c : num)) : num go "ohno")) in 42)) base-tenv)))

; serialize
(check-equal? (serialize (NumV 2)) "2")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (ClosV '() (NumC 2) '())) "#<procedure>")
(check-equal? (serialize (cast (unbox (Binding-value (top-env-primop-binding '+))) PrimopV)) "#<primop>")
(check-equal? (serialize (StrV "hello there")) "\"hello there\"")

; interp-many
(check-equal? (interp-many '() '()) '())
(check-equal? (interp-many (list (NumC 1) (NumC 4)) (top-env)) (list (NumV 1) (NumV 4)))

; bind-args
(check-equal? (bind-args '() '()) '())
(check-equal? (bind-args '(x y z) (list (NumV 8) (BoolV #f) (NumV 2)))
              (list (Binding 'x (box (NumV 8))) (Binding 'y (box (BoolV #f))) (Binding 'z (box (NumV 2)))))

; env-lookup
(check-equal? (env-lookup 'x (list (Binding 'x (box (NumV 4))))) (NumV 4))
(check-equal? (env-lookup 'y (list (Binding 'x (box (NumV 8)))
                                   (Binding 'y (box (BoolV #f))) (Binding 'z (box (NumV 2))))) (BoolV #f))
(check-exn (regexp (regexp-quote "[JYSS] Reference to undefined value: 'a"))
           (λ () (env-lookup 'a (list (Binding 'x (box (NumV 8)))
                                      (Binding 'y (box (BoolV #f))) (Binding 'z (box (NumV 2)))))))
(check-exn (regexp (regexp-quote "[JYSS] Reference to undefined value: 'x")) (λ () (env-lookup 'x '())))

; update-env
(check-exn (regexp (regexp-quote "[JYSS] Cannot update undefined binding: 'ohno"))
           (λ () (update-env (top-env) 'ohno (StrV "haha"))))

; type-env-lookup
(check-equal? (type-env-lookup 'x (list (TypedSymbol 'x 'NumT))) 'NumT)
(check-equal? (type-env-lookup 'y (list (TypedSymbol 'x 'StrT) (TypedSymbol 'y 'BoolT) (TypedSymbol 'z 'NumT))) 'BoolT)
(check-exn (regexp (regexp-quote "[JYSS] Reference to undefined type: 'a"))
           (λ () (type-env-lookup 'a (list (TypedSymbol 'x 'NumT) (TypedSymbol 'y 'BoolT) (TypedSymbol 'z 'StrT)))))

; top-env-primop-binding
(check-equal? ((PrimopV-op (cast (unbox (Binding-value (top-env-primop-binding '+))) PrimopV))
               (list (NumV 2) (NumV 4))) (NumV 6))

; interp-primop
(check-equal? (interp-primop 'num-eq? (list (NumV 2) (NumV 2))) (BoolV #t))
(check-equal? (interp-primop 'num-eq? (list (NumV 2) (NumV 1))) (BoolV #f))
(check-equal? (interp-primop 'str-eq? (list (StrV "cool") (StrV "cool"))) (BoolV #t))
(check-equal? (interp-primop '<= (list (NumV 2) (NumV 3))) (BoolV #t))
(check-equal? (interp-primop '<= (list (NumV 2) (NumV 2))) (BoolV #t))
(check-equal? (interp-primop '<= (list (NumV 2) (NumV 1))) (BoolV #f))
(check-equal? (interp-primop '+ (list (NumV 2) (NumV 4))) (NumV 6))
(check-equal? (interp-primop '- (list (NumV 2) (NumV 4))) (NumV -2))
(check-equal? (interp-primop '* (list (NumV 2) (NumV 4))) (NumV 8))
(check-equal? (interp-primop '/ (list (NumV 2) (NumV 4))) (NumV (/ 1 2)))
(check-exn (regexp (regexp-quote "[JYSS] Division by zero"))
           (λ () (interp-primop '/ (list (NumV 2) (NumV 0)))))
(check-exn (regexp (regexp-quote "[JYSS] Incorrect number of arguments on primitive operator: '*"))
           (λ () (interp-primop '* (list (NumV 1) (NumV 2) (NumV 3)))))
(check-exn (regexp (regexp-quote
                    "[JYSS] Nonnumeric value(s) passed to arithmetic binary operator: (BoolV #t) and (BoolV #f)"))
           (λ () (interp-primop 'num-equal (list (BoolV #t) (BoolV #f)))))
(check-exn (regexp (regexp-quote "[JYSS] Invalid primop: 'ohno"))
           (λ () (interp-primop 'ohno (list (NumV 1) (NumV 1)))))
(check-equal? (interp-primop 'substring (list (StrV "hello there") (NumV 3) (NumV 5))) (StrV "lo"))
(check-exn (regexp (regexp-quote "[JYSS] Incorrect arguments to substring: (list (NumV 1) (NumV 1) (NumV 1))"))
           (λ () (interp-primop 'substring (list (NumV 1) (NumV 1) (NumV 1)))))
(check-exn (regexp (regexp-quote "[JYSS] Improper bounds on substring: start 2, end 1"))
           (λ () (interp-primop 'substring (list (StrV "ohno") (NumV 2) (NumV 1)))))

; unreserved-symbol?
(check-equal? (unreserved-symbol? 'vars:) #f)
(check-equal? (unreserved-symbol? 'body:) #f)
(check-equal? (unreserved-symbol? 'rec:) #f)
(check-equal? (unreserved-symbol? 'if) #f)
(check-equal? (unreserved-symbol? 'proc) #f)
(check-equal? (unreserved-symbol? 'go) #f)
(check-equal? (unreserved-symbol? "ohno") #f)
(check-equal? (unreserved-symbol? 'x) #t)

; parse-type
(check-equal? (parse-type 'num) 'NumT)
(check-equal? (parse-type 'bool) 'BoolT)
(check-equal? (parse-type 'str) 'StrT)
(check-equal? (parse-type '(num bool -> str)) (FunT '(NumT BoolT) 'StrT))
(check-equal? (parse-type '((num -> num) -> (num -> num))) (FunT (list (FunT '(NumT) 'NumT)) (FunT '(NumT) 'NumT)))
(check-exn (regexp (regexp-quote "[JYSS] Unrecognized type: 'foo")) (λ () (parse-type '(num -> foo))))



;;> Extra Testcase set
#;(check-exn ;;> FAILED
 #px"JYSS"
(λ () (top-interp '(proc ([: : num]) go {+ : 1}))))

(check-exn ;;> OK
 #px"JYSS"
 (λ () (top-interp '(substring "hello" 3 1))))

(check-exn ;;> OK
 #px"JYSS"
 (λ () (top-interp '(substring "hello" 3))))

(check-exn ;;> OK
 #px"JYSS"
 (λ () (top-interp '(substring "hello" -3 1))))

#;(check-exn ;;> FAILED
 #px"JYSS"
 (λ () (top-interp '(substring "hello" 0.5 1))))

(check-exn ;;> OK
 #px"JYSS"
 (λ ()(type-check (parse '{proc {[a : (num -> [b : num])]} go 1234}) base-tenv)))

(check-not-exn ;;> OK
 (λ ()(top-interp '{{proc {[x : (num num -> num)]} go {x 3 4}} +})))

(check-exn ;;> OK
 #px"JYSS"
 (λ () (type-check (parse '{vars: [x : num = 3] body: {x 4 5}}) base-tenv)))

(check-exn ;;> OK
 #px"JYSS"
(λ () (top-interp '{rec: [f = {proc {[x : num]} : num go x}]
               in x})))
