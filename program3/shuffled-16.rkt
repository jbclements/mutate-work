#lang typed/racket

;;> eyeball: 6/6, Very nice

#|
Progress: All parts completed.
|#
(require typed/rackunit)
(define-syntax tstruct
    (syntax-rules ()
      [(_ name fields)
       (struct name fields #:transparent)]))

;data definition for arithmetic expressions
(define-type ExprC (U NumC StringC IdC AppC LamC))
(tstruct NumC ([n : Real]))
(tstruct StringC ([s : String]))
(tstruct IdC ([id : Symbol]))
(tstruct AppC ([fun : ExprC] [arg : (Listof ExprC)]))
(tstruct LamC ([params : (Listof Symbol)] [body : ExprC]))

;data definition for values
(define-type Value (U NumV StringV BoolV CloV PrimV))
(tstruct NumV ([n : Real]))
(tstruct StringV ([s : String]))
(tstruct BoolV ([b : Boolean]))
(tstruct CloV ([params : (Listof Symbol)]
               [body : ExprC]
               [env : Environment]))
(tstruct PrimV ([func : Symbol]))

;environment definiton
(define-type Environment (Immutable-HashTable Symbol Value))
(define top-env (make-immutable-hash
                 (list (cons '+ (PrimV '+))
                       (cons '- (PrimV '-))
                       (cons '* (PrimV '*))
                       (cons '/ (PrimV '/))
                       (cons 'if (PrimV 'if))
                       (cons '<= (PrimV '<=))
                       (cons 'equal? (PrimV 'equal?))
                       (cons 'true (BoolV true))
                       (cons 'false (BoolV false)))))

;accepts an sexpression of a function
;returns the result parsing and then evaluating the function
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

;accepts an expression and a list of functions
;evaluates/interprets the expression using the list of functions
(define (interp [e : ExprC] [env : Environment]) : Value
  (match e
    [(NumC n) (NumV n)]
    [(StringC s) (StringV s)]
    [(IdC i) (cond [(hash-has-key? env i) (hash-ref env i)]
                   [else (error 'interp "ZNQR: Id not found in environment ~e" i)])]
    [(AppC f a)
     #:when (equal? (PrimV 'if) (interp f env))
     (match (interp (first a) env)
       [(BoolV #t) (interp (second a) env)]
       [(BoolV #f) (interp (third a) env)]
       [else
        (error 'interp
               "ZNQR: if test should evaluate to a boolean ~e"
               (first a))])]
    [(AppC f a)
     (local [(define fn (interp f env))
             (define args (map (λ ([e : ExprC]) (interp e env)) a))]
       ;eagerly evaluates arguments before evaluating function
       (match fn
         [(PrimV op) ((getPrimFn fn) (first args) (second args))]
         [(CloV p b clo-env)
          (cond
            [(= (length p) (length args))
             (local [(define new-env (extend-env clo-env p args))]
               (interp b new-env))]
            [else (error 'interp "ZNQR: wrong number of arguments")])]
         [else (error 'interp "ZNQR: invalid function application")]))]
    [(LamC p b) (CloV p b env)]))

;accepts an sexpression
;returns equivalent form using the ExprC data definition
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? s) (NumC s)]
    [(? string? s) (StringC s)]
    [(? symbol? s)
     (cond
       [(reserved? s) (error 'parse "ZNQR: invalid id input ~e" s)]
       [else (IdC s)])]
    [(list 'if a ...)
     (cond
       [(not (= (length a) 3)) (error 'parse "ZNQR: wrong arity if ~e" s)]
       [else (AppC (IdC 'if) (list (parse (first a))
                                   (parse (second a))
                                   (parse (third a))))])]
    [(list 'var p ... b)
     (local [(define a (cast p Sexp))
             (define args (getVarArgs a))
             (define vals (getVarVals a))]
       (cond [(or (contains-reserved? args)
                  (contains-duplicate? args))
              (error 'parse "ZNQR: Given a reserved sym or duplicates ~e" args)]
             [else (AppC (LamC args (parse b)) vals)]))]
    [(list (list (? symbol? s) ...) '-> b)
     (local [(define args (cast s (Listof Symbol)))]
       (cond
         [(or (contains-reserved? args)
              (contains-duplicate? args))
          (error 'parse "ZNQR: Given a reserved sym or duplicates ~e" args)]
         [else (LamC args (parse b))]))]
    [(list (? symbol? op) a ...)
     #:when (hash-has-key? top-env op)
     (cond
       [(not (= (length a) 2)) (error 'parse "ZNQR: wrong arity binop ~e" s)]
       [else (AppC (IdC op) (list (parse (first a)) (parse (second a))))])]
    [(list name args ...) (AppC (parse name) (map parse args))]
    [else (error 'parse "ZNQR: invalid input ~e" s)]))

;===== Helpers =====
;given a value
;returns the string representation
(define (serialize [val : Value]) : String
  (match val
    [(NumV x) (~v x)]
    [(StringV x) x]
    [(BoolV b) (if b "true" "false")]
    [(PrimV s) "#<primop>"]
    [(CloV params body env) "#<procedure>"]))

;accepts a symbol
;returns whether it is a reserved operator or keyword
(define (reserved? [sym : Symbol]) : Boolean
  (or (symbol=? sym 'if)
      (symbol=? sym 'var)
      (symbol=? sym '->)
      (symbol=? sym '=)))

;given an sexp
;returns a list of variable argument names
(define (getVarArgs [s : Sexp]) : (Listof Symbol)
  (match s
    ['() s]
    [(list (list (? symbol? id) '= exp) rest ...) (cons id (getVarArgs rest))]
    [_ (error 'getVarArgs "ZNQR: Variable identifier must be a symbol ~e" s)]))

;given an sexp
;returns a list of variable argument values
(define (getVarVals [s : Sexp]) : (Listof ExprC)
  (match s
    ['() s]
    [(list (list (? symbol? id) '= exp) rest ...) (cons (parse exp)
                                                        (getVarVals rest))]))

;given a list of symbols
;returns if the list contains a duplicate of the symbol
(define (contains-duplicate? [syms : (Listof Symbol)]) : Boolean
  (cond
    [(empty? syms) false]
    [else (or (contains? (first syms) (rest syms))
              (contains-duplicate? (rest syms)))]))

;given a list of symbols
;returns if the list contains a reserved symbol
(define (contains-reserved? [syms : (Listof Symbol)]) : Boolean
  (ormap reserved? syms))

;given a symbol and a list of symbols
;returns if the symbol is in the list
(define (contains? [sym : Symbol] [l : (Listof Symbol)]) : Boolean
  (ormap (λ ([x : Symbol]) (symbol=? x sym)) l))

;given an environment a list of symbols and Values
;returns an extended environment with those bindings
(define (extend-env [e : Environment]
                    [s : (Listof Symbol)]
                    [v : (Listof Value)]) : Environment
  (cond
    [(empty? s) e]
    [else
     (local [(define new-env (hash-set e (first s) (first v)))]
       (extend-env new-env (rest s) (rest v)))]))

;Compute a+b.
;Signal an error if either a or b is not a number.
(define add : (-> Value Value NumV)
  (λ ([a : Value] [b : Value])
    (match (list a b)
      [(list (? NumV? a) (? NumV? b)) (NumV (+ (NumV-n a) (NumV-n b)))]
      [else (error 'add "ZNQR: Given input not a number")])))

;Compute a-b.
;Signal an error if either a or b is not a number.
(define sub : (-> Value Value NumV)
  (λ ([a : Value] [b : Value])
    (match (list a b)
      [(list (? NumV? a) (? NumV? b)) (NumV (- (NumV-n a) (NumV-n b)))]
      [else (error 'sub "ZNQR: Given input not a number")])))

;Compute a+b.
;Signal an error if either a or b is not a number.
(define mult : (-> Value Value NumV)
  (λ ([a : Value] [b : Value])
    (match (list a b)
      [(list (? NumV? a) (? NumV? b)) (NumV (* (NumV-n a) (NumV-n b)))]
      [else (error 'mult "ZNQR: Given input not a number")])))

;Compute a/b.
;Signal an error if either a or b is not a number.
(define div : (-> Value Value NumV)
  (λ ([a : Value] [b : Value])
    (match (list a b)
      [(list (? NumV? a) (? NumV? b))
       (cond [(equal? (NumV-n b) 0) (error 'div "ZNQR: Cannot divide by zero")]
          [else (NumV (/ (NumV-n a) (NumV-n b)))])]
      [else (error 'div "ZNQR: Given input not a number")])))

;Compute a<=b.
;Signal an error if either a or b is not a number.
(define leq : (-> Value Value BoolV)
  (λ ([a : Value] [b : Value])
    (match (list a b)
      [(list (? NumV? a) (? NumV? b)) (BoolV (<= (NumV-n a) (NumV-n b)))]
      [else (error 'leq "ZNQR: Given input not a number")])))

;Return true if neither value is a closure or a primitive operator
;and the two values are equal
(define eq? : (-> Value Value BoolV)
  (λ ([a : Value] [b : Value])
    (match (list a b)
      [(list (? NumV? an) (? NumV? bn))
       (BoolV (equal? (NumV-n an) (NumV-n bn)))]
      [(list (? BoolV? an) (? BoolV? bn))
       (BoolV (equal? (BoolV-b an) (BoolV-b bn)))]
      [(list (? StringV? an) (? StringV? bn))
       (BoolV (equal? (StringV-s an) (StringV-s bn)))]
      [else (BoolV #f)])))

;given a PrimV return its
;corresponding value function
(define (getPrimFn [p : PrimV]) : (-> Value Value Value)
  (match p
    [(PrimV '+) add]
    [(PrimV '-) sub]
    [(PrimV '*) mult]
    [(PrimV '/) div]
    [(PrimV '<=) leq]
    [(PrimV 'equal?) eq?]))

;====== Test Cases ======
; [TEST] top-interp
(check-equal? (top-interp '{+ 1 2}) "3")
(check-equal? (top-interp '{- 1 2}) "-1")
(check-equal? (top-interp '{* 1 2}) "2")
(check-equal? (top-interp '{/ 1 2}) "1/2")
(check-equal? (top-interp '{<= 1 2}) "true")
(check-equal? (top-interp '{equal? 2 2}) "true")
(check-equal? (top-interp '{equal? 1 2}) "false")
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '{{a b c} -> 3}) "#<procedure>")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {x = false}
                                {if {equal? {<= y 100} x}
                                    {+ z y}
                                    {- y z}}})
              "75")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {x = false}
                                {if {equal? {<= y 90} x}
                                    +
                                    {{a b c} -> 3}}})
              "#<primop>")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {x = false}
                                {if {equal? {<= y 100} x}
                                    +
                                    {{a b c} -> 3}}})
              "#<procedure>")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {x = false}
                                {if {equal? {<= y 100} x}
                                    {/ y 0}
                                    {{a b c} -> 3}}})
              "#<procedure>")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {x = true}
                                {if {equal? {<= {+ z y} 100} x}
                                    "less than or equal to 100"
                                    "greater than 100"}})
              "greater than 100")
(check-equal? (top-interp '{var {a = {- {* 2 5} 23}}
                                {b = 0}
                                {<= a b}})
              "true")
(check-equal? (top-interp '{var {z = {+ 9 14}}
                                {y = 98}
                                {+ z y}})
              "121")
(check-equal? (top-interp '{{{z y} -> {+ z y}}
                            {+ 9 14}
                            98})
              "121")
(check-equal? (top-interp '{{{close} -> {close}}
                            {{{test} -> {{} -> {test {+ 1 1} {- 23 10}}}}
                             {{a b} -> {* a {+ 2 b}}}}})
              "30")
(check-exn #px"ZNQR: wrong number of arguments"
           (λ () (top-interp '{{{z y} -> {+ z y}}
                               {+ 9 14}
                               98
                               1})))
(check-exn #px"ZNQR: wrong arity binop"
           (λ () (top-interp '{var {z = {+ 9 14 1}}
                                        {y = 98}
                                        {+ z y}})))
(check-exn #px"ZNQR: wrong arity binop"
           (λ () (top-interp '{var {z = {+ 9 14}}
                                        {y = 98}
                                        {+ z y 1}})))
(check-exn #px"ZNQR: wrong arity binop"
           (λ () (top-interp '{var {z = {+ 9}}
                                        {y = 98}
                                        {+ z y 1}})))
(check-exn #px"ZNQR: Given a reserved sym or duplicates"
           (λ () (top-interp '{var {z = {+ 9 14}}
                                   {z = 98}
                                   {+ z y 1}})))
(check-exn #px"ZNQR: Given a reserved sym or duplicates"
           (λ () (top-interp '{{{z z} -> {+ z z}}
                                    {+ 9 14}
                                    98})))
(check-exn #px"ZNQR: invalid function application"
           (λ () (top-interp '{"+" 1 2})))
(check-exn #px"ZNQR: invalid function application"
           (λ () (top-interp '{0 1 2})))
(check-exn #px"ZNQR: wrong arity if"
           (λ () (top-interp '{var {z = {+ 9 14}}
                                   {y = 98}
                                   {x = false}
                                   {if {equal? {<= y 100} x}
                                       {+ z y}}})))
(check-exn #px"ZNQR: wrong arity if"
           (λ () (top-interp '{var {z = {+ 9 14}}
                                   {y = 98}
                                   {x = false}
                                   {if {equal? {<= y 100} x}
                                       {+ z y}
                                       {- y z}
                                       {/ z y}}})))
(check-exn #px"ZNQR: if test should evaluate to a boolean"
           (λ () (top-interp '{var {z = {+ 9 14}}
                                   {y = 98}
                                   {x = 1}
                                   {if {+ y x}
                                       {+ z y}
                                       {- y z}}})))
(check-exn #px"ZNQR: Variable identifier must be a symbol"
           (λ () (top-interp '{var {"a" = {- {* 2 5} 23}}
                                   {b = 0}
                                   {<= a b}})))
(check-exn #px"ZNQR: Given input not a number"
           (λ () (top-interp '{var {z = {+ 9 14}}
                                   {y = 98}
                                   {x = false}
                                   {if {equal? {<= "y" 100} x}
                                       {+ z y}
                                       {- y z}}})))
(check-exn #px"ZNQR: Given input not a number"
           (λ () (top-interp '{+ 1 "test"})))
(check-exn #px"ZNQR: Given input not a number"
           (λ () (top-interp '{<= 1 "test"})))

; [TEST] parse
(check-equal? (parse '1) (NumC 1))
(check-equal? (parse '"test") (StringC "test"))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '{f a})
              (AppC (IdC 'f) (list (IdC 'a))))
(check-equal? (parse '{+ 1 2})
              (AppC (IdC '+) (list (NumC 1)
                                   (NumC 2))))
(check-equal? (parse '{* 1 2})
              (AppC (IdC '*) (list (NumC 1)
                                   (NumC 2))))
(check-equal? (parse '{<= 1 2})
              (AppC (IdC '<=) (list (NumC 1)
                                    (NumC 2))))
(check-equal? (parse '{equal? 1 2})
              (AppC (IdC 'equal?) (list (NumC 1)
                                        (NumC 2))))
(check-equal? (parse '{if {<= 1 0} 1 0})
              (AppC (IdC 'if) (list (AppC (IdC '<=) (list (NumC 1) (NumC 0)))
                                    (NumC 1)
                                    (NumC 0))))
(check-equal? (parse '{var {z = {+ 9 14}}
                           {y = 98}
                           {+ z y}})
              (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z)
                                                            (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9)
                                               (NumC 14)))
                          (NumC 98))))
(check-equal? (parse '{{z y} -> {+ z y}})
              (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z)
                                                      (IdC 'y)))))
(check-equal? (parse '{{{z y} -> {+ z y}}
                       {+ 9 14}
                       98})
              (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z)
                                                            (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9)
                                               (NumC 14)))
                          (NumC 98))))
(check-exn #px"ZNQR: invalid input"
           (λ ()
             (parse #f)))
(check-exn #px"ZNQR: wrong arity binop"
           (λ ()
             (parse '{+ 1 2 3})))
(check-exn #px"ZNQR: wrong arity binop"
           (λ ()
             (parse '{+ 1})))
(check-exn #px"ZNQR: invalid id input"
           (λ ()
             (parse 'if)))
(check-exn #px"ZNQR: wrong arity if"
           (λ ()
             (parse '{if {<= 1 0} 1})))
(check-exn #px"ZNQR: wrong arity if"
           (λ ()
             (parse '{if {<= 1 0} 1 0 2})))
(check-exn #px"ZNQR: invalid id input"
           (λ ()
             (parse '{= a b})))
(check-exn #px"ZNQR: Given a reserved sym or duplicates"
           (λ ()
             (parse '{var {z = {+ 9 14}}
                          {z = 98}
                          {+ z y 1}})))
(check-exn #px"ZNQR: Given a reserved sym or duplicates"
           (λ ()
             (parse '{{{z z} -> {+ z z}}
                      {+ 9 14}
                      98})))

; [TEST] interp
(check-equal? (interp (NumC 0) top-env) (NumV 0))
(check-equal? (interp (StringC "0") top-env) (StringV "0"))
(check-equal? (interp (IdC '+) top-env) (PrimV '+))
(check-equal? (interp (AppC (IdC '+) (list (NumC 1)
                                           (NumC 2)))
               top-env)
              (NumV 3))
(check-equal? (interp (AppC (IdC '-) (list (NumC 1)
                                           (NumC 2)))
               top-env)
              (NumV -1))
(check-equal? (interp (AppC (IdC '*) (list (NumC 1)
                                           (NumC 2)))
               top-env)
              (NumV 2))
(check-equal? (interp (AppC (IdC '/) (list (NumC 1)
                                           (NumC 2)))
               top-env)
              (NumV 1/2))
(check-equal? (interp (AppC (IdC 'if) (list (AppC (IdC '<=) (list (NumC 1) (NumC 1)))
                                            (NumC 1)
                                            (NumC 2)))
               top-env)
              (NumV 1))
(check-equal? (interp (AppC (IdC 'if) (list (AppC (IdC '<=) (list (NumC 2) (NumC 1)))
                                            (NumC 1)
                                            (NumC 2)))
               top-env)
              (NumV 2))
(check-equal? (interp (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z)
                                                              (IdC 'y))))
                      top-env)
              (CloV '(z y) (AppC (IdC '+) (list (IdC 'z)
                                                (IdC 'y)))
                    top-env))
(check-equal? (interp
               (AppC (LamC (list 'z 'y) (AppC (IdC '+) (list (IdC 'z)
                                                             (IdC 'y))))
                     (list (AppC (IdC '+) (list (NumC 9)
                                                (NumC 14)))
                           (NumC 98)))
               top-env)
              (NumV 121))
(check-exn #px"ZNQR: Id not found in environment"
           (λ ()
             (interp (IdC 'f) top-env)))
(check-exn #px"ZNQR: if test should evaluate to a boolean"
           (λ ()
             (interp (parse '{var {z = {+ 9 14}}
                                  {y = 98}
                                  {x = 1}
                                  {if {+ y x}
                                      {+ z y}
                                      {- y z}}}) top-env)))
(check-exn #px"ZNQR: wrong number of arguments"
           (λ ()
             (interp (AppC (LamC (list 'z 'y 'x) (AppC (IdC '+) (list (IdC 'z)
                                                                      (IdC 'y))))
                           (list (AppC (IdC '+) (list (NumC 9)
                                                      (NumC 14)))
                                 (NumC 98))) top-env)))
(check-exn #px"ZNQR: invalid function application"
           (λ ()
             (interp (AppC (StringC "not a closure or prim")
                           (list (AppC (IdC '+) (list (NumC 9)
                                                      (NumC 14)))
                                 (NumC 98))) top-env)))

;====== Helpers Tests =====
; [TEST] serialize
(check-equal? (serialize (NumV 3)) "3")
(check-equal? (serialize (StringV "three")) "three")
(check-equal? (serialize (BoolV #t)) "true")
(check-equal? (serialize (BoolV #f)) "false")
(check-equal? (serialize (PrimV '+)) "#<primop>")
(check-equal? (serialize (CloV '(a b) (LamC '(a b) (IdC 'a)) top-env))
              "#<procedure>")

; [TEST] reserved?
(check-equal? (reserved? 'if) #t)
(check-equal? (reserved? 'var) #t)
(check-equal? (reserved? '->) #t)
(check-equal? (reserved? '=) #t)
(check-equal? (reserved? '+) #f)

; [TEST] getVarArgs
(check-equal? (getVarArgs '{{z = {+ 9 14}}
                            {y = 98}})
              (list 'z 'y))
(check-exn #px"ZNQR: Variable identifier must be a symbol"
           (λ () (getVarArgs '{{"a" = {- {* 2 5} 23}}
                               {b = 0}})))

; [TEST] getVarVals
(check-equal? (getVarVals '{{z = {+ 9 14}}
                            {y = 98}})
              (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))
                    (NumC 98)))

; [TEST] contains-duplicate?
(check-equal? (contains-duplicate? '()) #f)
(check-equal? (contains-duplicate? '(x y z)) #f)
(check-equal? (contains-duplicate? '(x y z x)) #t)

; [TEST] contains-reserved?
(check-equal? (contains-reserved? '(a = b)) #t)
(check-equal? (contains-reserved? '(a b -> a)) #t)
(check-equal? (contains-reserved? '(x y)) #f)

; [TEST] contains?
(check-equal? (contains? 'x '()) #f)
(check-equal? (contains? 'x '(x y z)) #t)
(check-equal? (contains? 'a '(x y z)) #f)

; [TEST] extend-env
(check-equal? (extend-env top-env '(x y) (list (NumV 1) (NumV 2)))
              (make-immutable-hash
               (list (cons 'x (NumV 1))
                     (cons 'y (NumV 2))
                     (cons '+ (PrimV '+))
                     (cons '- (PrimV '-))
                     (cons '* (PrimV '*))
                     (cons '/ (PrimV '/))
                     (cons 'if (PrimV 'if))
                     (cons '<= (PrimV '<=))
                     (cons 'equal? (PrimV 'equal?))
                     (cons 'true (BoolV true))
                     (cons 'false (BoolV false)))))

; [TEST] add
(check-equal? (add (NumV 1) (NumV 3)) (NumV 4))
(check-exn #px"ZNQR: Given input not a number"
           (λ ()
             (add (NumV 1) (BoolV #t))))

; [TEST] sub
(check-equal? (sub (NumV 1) (NumV 3)) (NumV -2))
(check-exn #px"ZNQR: Given input not a number"
           (λ ()
             (sub (NumV 1) (StringV "test"))))

; [TEST] mult
(check-equal? (mult (NumV 1) (NumV 3)) (NumV 3))
(check-exn #px"ZNQR: Given input not a number"
           (λ ()
             (mult (NumV 1) (StringV "test"))))

; [TEST] div
(check-equal? (div (NumV 1) (NumV 3)) (NumV 1/3))
(check-exn #px"ZNQR: Cannot divide by zero"
           (λ ()
             (div (NumV 10) (NumV 0))))
(check-exn #px"ZNQR: Given input not a number"
           (λ ()
             (div (NumV 1) (StringV "test"))))

; [TEST] leq
(check-equal? (leq (NumV 1) (NumV 3)) (BoolV #t))
(check-equal? (leq (NumV 3) (NumV 3)) (BoolV #t))
(check-equal? (leq (NumV 4) (NumV 3)) (BoolV #f))
(check-exn #px"ZNQR: Given input not a number"
           (λ ()
             (leq (NumV 1) (StringV "test"))))

; [TEST] eq?
(check-equal? (eq? (NumV 1) (NumV 3)) (BoolV #f))
(check-equal? (eq? (NumV 3) (NumV 3)) (BoolV #t))
(check-equal? (eq? (NumV 4) (NumV 3)) (BoolV #f))
(check-equal? (eq? (BoolV #t) (BoolV #t)) (BoolV #t))
(check-equal? (eq? (BoolV #t) (BoolV #f)) (BoolV #f))
(check-equal? (eq? (StringV "yes") (StringV "yes")) (BoolV #t))
(check-equal? (eq? (StringV "yes") (StringV "no")) (BoolV #f))
(check-equal? (eq? (NumV 4) (BoolV #t)) (BoolV #f))
(check-equal? (eq? (BoolV #t) (StringV "yes")) (BoolV #f))

; [TEST] getPrimFn
(check-equal? (getPrimFn (PrimV '+)) add)
(check-equal? (getPrimFn (PrimV '-)) sub)
(check-equal? (getPrimFn (PrimV '*)) mult)
(check-equal? (getPrimFn (PrimV '/)) div)
(check-equal? (getPrimFn (PrimV '<=)) leq)
(check-equal? (getPrimFn (PrimV 'equal?)) eq?)
