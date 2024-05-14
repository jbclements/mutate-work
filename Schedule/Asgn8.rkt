#lang typed/racket
(require typed/rackunit)

;; it's done. passes everything.

;; Defining data types for the program.
(define-type ExprC (U NumC IfC IdC AppC LamC StrC Boolean ArrC MutC BegC RecC))
(struct NumC ([n : Real]) #:transparent)
(struct IdC  ([s : Symbol]) #:transparent)
(struct LamC ([arg : (Listof Symbol)] [type : (Listof Ty)] [body : ExprC]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IfC ([then : ExprC] [con : ExprC] [else : ExprC]) #:transparent)
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)]) #:transparent)
(struct ArrC ([arr : (Listof ExprC)]) #:transparent)
(struct MutC ([var : Symbol] [val : ExprC]) #:transparent)
(struct BegC ([var : (Listof ExprC)]) #:transparent)
(struct RecC ([name : Symbol] [arg : (Listof Symbol)]
                              [type : (Listof Ty)] [ret : Ty] [body : ExprC] [call : ExprC]) #:transparent)

(define-type Ty (U num bool str void fun numarray))
(struct num () #:transparent)
(struct bool () #:transparent)
(struct str () #:transparent)
(struct void () #:transparent)
(struct numarray () #:transparent)
(struct fun ([argT : (Listof Ty)] [retT : Ty]) #:transparent)

(define-type Value (U numV boolV closV primV strV arrV voidV))
(define boxi (inst box Integer))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct closV ([arg : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primV ([oper : Symbol]) #:transparent)
(struct strV ([s : String]) #:transparent)
(struct arrV ([arr : (Vectorof Integer)]) #:transparent)
(struct voidV () #:transparent)

(struct Binding ((name : (U Boolean String Symbol)) (val : (Boxof Value))) #:transparent)
(define extend-env cons)
(define-type Env (Listof Binding))
(define top-env  (list (Binding 'true (box (boolV #t)))
                       (Binding 'false (box (boolV #f)))
                       (Binding '+ (box (primV '+)))
                       (Binding '- (box (primV '-)))
                       (Binding '* (box (primV '*)))
                       (Binding '/ (box (primV '/)))
                       (Binding '<= (box (primV '<=)))
                       (Binding 'num-eq? (box (primV 'num-eq?)))
                       (Binding 'str-eq? (box (primV 'str-eq?)))
                       (Binding 'substring (box (primV 'substring)))
                       (Binding 'arr (box (primV 'arr)))
                       (Binding 'aref (box (primV 'aref)))
                       (Binding 'aset (box (primV 'aset)))
                       (Binding 'alen (box (primV 'alen)))
                       (Binding 'error (box (primV 'error)))))

(struct TypeBinding ((name : Symbol) (val : Ty)) #:transparent)
(define extend-ty-env cons)
(define-type TypeEnv (Listof TypeBinding))
(define base-tenv  (list (TypeBinding 'num (num))
                        (TypeBinding 'bool (bool))
                        (TypeBinding 'true (bool))
                        (TypeBinding 'false (bool))
                        (TypeBinding 'str (str))
                        (TypeBinding 'void (void))
                        (TypeBinding 'numarray (numarray))
                        (TypeBinding '+ (fun (list (num) (num)) (num)))
                        (TypeBinding '- (fun (list (num) (num)) (num)))
                        (TypeBinding '/ (fun (list (num) (num)) (num)))
                        (TypeBinding '* (fun (list (num) (num)) (num)))
                        (TypeBinding '<= (fun (list (num) (num)) (bool)))
                        (TypeBinding 'num-eq? (fun (list (num) (num)) (bool)))
                        (TypeBinding 'str-eq? (fun (list (str) (str)) (bool)))
                        (TypeBinding 'substring (fun (list (str) (num) (num)) (str)))
                        (TypeBinding 'arr (fun (list (num) (num)) (numarray)))
                        (TypeBinding 'aref (fun (list (numarray) (num)) (num)))
                        (TypeBinding 'aset (fun (list (numarray) (num) (num)) (void)))
                        (TypeBinding 'alen (fun (list (numarray)) (num)))))

;; Reserved? checks if input is a reserved Sexp or not.
(define (reserved? [s : Sexp]) : Boolean
  (match s
    ['where #t]
    ['if #t]
    ['else #t]
    [':= #t]
    ['letrec #t]
    ['-> #t]
    ['<- #t]
    [': #t]
    ['begin #t]
    ['in #t]
    ['makearr #t]
    [other #f]))

 
;; Parse parses Sexp to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    ;;number
    [(? real? n) (NumC n)]
    ;;symbol
    [(? symbol? s) (if (reserved? s)
                       (error 'parse "VVQS - reserved operator ~e" s)
                       (IdC s))]
    ;;string
    [(? string? str) (StrC str)]
    ;;boolean
    [(? boolean? b) b]
    ;;if
    [(list a 'if b 'else c) (IfC (parse a) (parse b) (parse c))]
    ;;LamC
    [(list (list (list (? symbol? a) ': b) ...) '=> x)
     (define args (cast a (Listof Symbol)))
     (if (no-duplicates? args)
         (if (ormap reserved? args)
             (error 'parse "VVQS5 - error ~e: " a)
             (LamC args (for/list : (Listof Ty)
                          ([sexp (cast b (Listof Sexp))]) (parse-type sexp)) (parse x)))
         (error 'parse "VVQS5 - error ~e: " a))]
    ;;ArrC
    [(list 'makearr a ...) (ArrC (for/list : (Listof ExprC)
                                   ([sexp a]) (parse sexp)))]
    ;;MutC
    [(list (? symbol? a) '<- b) (MutC a (parse b))]
    ;;BegC
    [(list 'begin exp ...) (BegC (for/list : (Listof ExprC)
                                   ([sexp exp]) (parse sexp)))]
    ;;where
    [(list a 'where (list (list (list var ': type) ':= val) ...))
     (define args (cast var (Listof Sexp)))
     (define types (cast type (Listof Sexp)))
     (if (ormap reserved? args)
         (error 'parse "VVQS")
         (parse (cons (list (for/list : (Listof Sexp) ([x args] [y types])
                              (list x ': y)) '=> a) (cast val (Listof Sexp)))))]
    ;;RecC
    [(list 'letrec (list (? symbol? name) (list (list (? symbol? a) ': b) ...) ': (? symbol? c) '=> body) 'in call)
     (define args (cast a (Listof Symbol)))
     (if (no-duplicates? args)
         (if (or (ormap reserved? args) (reserved? name))
             (error 'parse "VVQS5 - error ~e: " a)
             (RecC name args (for/list : (Listof Ty)
                               ([sexp (cast b (Listof Sexp))]) (parse-type sexp))
                   (parse-type c) (parse body) (parse call)))
         (error 'parse "VVQS5 - error ~e: " a))]
    ;;AppC
    [(list a b ...)
     (AppC (parse a)
           (for/list : (Listof ExprC)
             ([sexp b]) (parse sexp)))]
    [other (error 'parse "VVQS")]))





;; Parse VVQS' type to racket's type
(define (parse-type [s : Sexp]) : Ty
  (match s
    ['num (num)]
    ['bool (bool)]
    ['str (str)]
    ['void (void)]
    ['numarray (numarray)]
    [(list a ... '-> b) (fun (for/list : (Listof Ty)
                               ([sexp (cast a (Listof Sexp))]) (parse-type sexp)) (parse-type b))]
    [other (error 'parse-type "VVQS ~e" s)]))

;; No-duplicates checks if there are any duplicate variables during parsing.
(define (no-duplicates? [lst : (Listof Symbol)]) : Boolean
  (define (helper [seen : (Listof Symbol)] [lst : (Listof Symbol)]) : Boolean
    (cond
      [(empty? lst) #t]
      [(member (first lst) seen) #f]
      [else (helper (cons (first lst) seen) (rest lst))]))
  (helper '() lst))


;; Lookup looks up symbol in type environment and return the type if exists.
(define (lookup-type [s : Symbol] [tenv : (Listof TypeBinding)]) : Ty
  (match tenv
    ['() (error 'lookup-type "name not found - VVQS ~e" s)]
    [(cons (TypeBinding name val) r) (cond
                                       [(equal? s name) val]
                                       [else (lookup-type s r)])]))

;; Type-check an expression
(define (type-check [e : ExprC] [tenv : TypeEnv]) : Ty
  (match e
    [(NumC n) (num)]
    [(IdC s) (lookup-type s tenv)]
    [(? boolean? b) (bool)]
    [(StrC s) (str)]
    [(LamC arg type body) (fun type (type-check body
                                                (append tenv (for/list : (Listof TypeBinding) ([a arg] [b type])
                                                               (TypeBinding a b)))))]   
    [(IfC then con else) (if (bool? (type-check con tenv))
                             (if (equal? (type-check then tenv) (type-check else tenv))
                                 (type-check then tenv)
                                 (error 'type-check "Expected the same type for then and else - VVQS"))
                             (error 'type-check "Expected a boolean in if - VVQS"))]
    [(ArrC arr) (if (andmap num? (for/list : (Listof Ty) ([a arr])
                                   (type-check a tenv)))
                    (numarray)
                    (error 'type-check "Improper type in array - VVQS"))]
    [(MutC var val) (if (equal? (lookup-type var tenv) (type-check val tenv))
                        (void)
                        (error 'type-check "Mutation does not have the same type - VVQS"))]
    [(BegC var) (last (for/list : (Listof Ty) ([i var]) (type-check i tenv)))]
    [(AppC f arg) (let ([ft (type-check f tenv)]
                        [at (for/list : (Listof Ty) ([a arg]) (type-check a tenv))])
                    (cond
                      [(not (fun? ft))
                       (error 'tc "not a function - VVQS")]
                      [(not (equal? (fun-argT ft) at))
                       (error 'type-check "app arg mismatch - VVQS ~e" f)]
                      [else (fun-retT ft)]))]
    [(RecC f a aT rT b u)
     (let ([extended-env
            (extend-ty-env (TypeBinding f (fun aT rT)) tenv)])
       (cond
         [(not (equal? rT (type-check b
                                      (append extended-env (for/list : (Listof TypeBinding) ([i a] [j aT])
                                                             (TypeBinding i j))))))
          (error 'type-check "body return type not correct - VVQS")]
         [else (type-check u extended-env)]))]))



;; Lookup looks up symbol in environment and return the value if exists.
(define (lookup [for : Symbol] [env : (Listof Binding)]) : (Boxof Value)
  (match env
    ['() (error 'lookup "name not found - VVQS ~e" for)]
    [(cons (Binding name val) r) (cond
                                   [(equal? for name) val]
                                   [else (lookup for r)])]))


;; Arith is a helper functions to perform arith or comparisons of Values.
(define (arith [op : primV] [args : (Listof Value)])
  (match op
    [(primV '+) (numV (+ (numV-n (cast (first args) numV)) (numV-n (cast (second args) numV))))]
    [(primV '-) (numV (- (numV-n (cast (first args) numV)) (numV-n (cast (second args) numV))))]
    [(primV '*) (numV (* (numV-n (cast (first args) numV)) (numV-n (cast (second args) numV))))]
    [(primV '/) (if (equal? (second args) (numV 0)) (error 'arith "VVQS division by zero")
                    (numV (/ (numV-n (cast (first args) numV)) (numV-n (cast (second args) numV)))))]
    [(primV '<=) (if (<= (numV-n (cast (first args) numV)) (numV-n (cast (second args) numV)))
                     (boolV #t) (boolV #f))]
    [(primV 'num-eq?) (if (equal? (first args) (second args)) (boolV #t) (boolV #f))]
    [(primV 'str-eq?) (if (equal? (first args) (second args)) (boolV #t) (boolV #f))]
    [(primV 'substring) (strV (substring (strV-s (cast (first args) strV))
                                         (exact-round (numV-n (cast (second args) numV)))
                                         (exact-round (numV-n (cast (list-ref args 2) numV)))))]
    [(primV 'arr) (arrV (make-vector
                         (exact-round (numV-n (cast (first args) numV)))
                         (exact-round (numV-n (cast (second args) numV)))))]
    [(primV 'aref) (numV (vector-ref (arrV-arr (cast (first args) arrV))
                                     (exact-round (numV-n (cast (second args) numV)))))]
    [(primV 'aset) (vector-set! (arrV-arr (cast (first args) arrV))
                                (exact-round (numV-n (cast (second args) numV)))
                                (exact-round (numV-n (cast (list-ref args 2) numV)))) (voidV)]
    [(primV 'alen) (numV (vector-length (arrV-arr (cast (first args) arrV))))]))


;; Interp interprets ExprC and adds variables to environments.
;; Will return Value, and will need to be serialized.
(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumC n) (numV n)]
    [(IdC n) (unbox (lookup n env))]
    [(? boolean? b) (boolV b)]
    [(LamC arg type body) (closV arg body env)]
    [(StrC s) (strV s)]
    [(ArrC arr) (define lst (map numV-n (for/list : (Listof numV) ([i arr]) (cast (interp i env) numV))))
                (if (andmap integer? lst)
                    (arrV (apply vector (map exact-round lst)))
                    (error 'interp "must be integers numarray - VVQS"))]
    [(IfC tru cond else) (define if-cond (interp cond env))
                         (if (equal? if-cond (boolV #t))
                             (interp tru env)
                             (interp else env))]
    [(MutC var val) (set-box! (lookup var env) (interp val env)) (voidV)]
    [(BegC exp) (last (for/list : (Listof Value) ([i exp]) (interp i env)))]
    [(AppC f a) (define f-value (interp f env))    
                (if (primV? f-value)
                    (arith f-value (for/list : (Listof Value) ([i a]) (interp i env)))
                    (interp (closV-body (cast f-value closV))
                                (append (map Binding (closV-arg (cast f-value closV))
                                             (for/list : (Listof (Boxof Value)) ([lst a])
                                               (box (interp lst env))))
                                        (closV-env (cast f-value closV)))))]
    [(RecC f a ty ret body call) (define extended (extend-env (Binding f (box (numV 0))) env))
                                 (set-box! (lookup f extended) (closV a body extended))
                                 (interp call extended)]))


;; Serialize converts Values to readable string on output.
(define (serialize [a : Value]) : String
  (match a
    [(? numV? n) (~v (numV-n n))]
    [(? boolV? b) (if (equal? (boolV-b b) #t) "true" "false")]
    [(? strV? s) (strV-s s)]
    [(? closV? e) "#<procedure>"]
    [(? primV? oper) "#<primop>"]
    [(? voidV?) "#<void>"]
    [(? arrV? arr) "#<array>"]))


;; Top interp simplifies which functions to use so Sexp can be converted directly to String.
(define (top-interp [s : Sexp]) : String
  (define parsed (parse s))
  (type-check parsed base-tenv)
  (serialize (interp parsed top-env)))


;;reserved
(check-equal? (reserved? 'where) #t)
(check-equal? (reserved? 'if) #t)
(check-equal? (reserved? 'else) #t)
(check-equal? (reserved? ':=) #t)
(check-equal? (reserved? 'letrec) #t)
(check-equal? (reserved? '->) #t)
(check-equal? (reserved? '<-) #t)
(check-equal? (reserved? ':) #t)
(check-equal? (reserved? 'begin) #t)
(check-equal? (reserved? 'in) #t)
(check-equal? (reserved? 'makearr) #t)
(check-equal? (reserved? 'a) #f)

;;parse-type
(check-equal? (parse-type 'num) (num))
(check-equal? (parse-type 'bool) (bool))
(check-equal? (parse-type 'str) (str))
(check-equal? (parse-type 'void) (void))
(check-equal? (parse-type 'numarray) (numarray))
(check-equal? (parse-type '(num -> str)) (fun (list (num)) (str)))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse-type '(+ + +))))

;;parse
(check-equal? (parse 1) (NumC 1))
(check-equal? (parse 's) (IdC 's))
(check-equal? (parse "s") (StrC "s"))
(check-equal? (parse #t) #t)
(check-equal? (parse '(1 if {<= 2 1} else 0)) (IfC (NumC 1) (AppC (IdC '<=) (list (NumC 2) (NumC 1))) (NumC 0)))
(check-equal? (parse '{makearr 1 2 3}) (ArrC (list (NumC 1) (NumC 2) (NumC 3))))
(check-equal? (parse '{a <- 2}) (MutC 'a (NumC 2)))
(check-equal? (parse '{begin {+ x y} {x <- 3}})
              (BegC (list (AppC (IdC '+) (list (IdC 'x) (IdC 'y))) (MutC 'x (NumC 3)))))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse '{{[x : num] [if : str]} => {+ x if}})))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse '{{+ z if}
                               where
                               {[[z : num] := {+ 9 14}] [[if : num] := 98]}})))

;;type-check
(check-equal? (type-check #t base-tenv) (bool))
(check-equal? (type-check (ArrC (list (NumC 1))) base-tenv) (numarray))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (type-check (ArrC (list (StrC "a"))) base-tenv)))
(check-equal? (type-check (parse '{{begin {x <- 3} {+ x y}}
                                   where {[[x : num] := 1] [[y : num] := 2]}}) base-tenv) (num))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (type-check (parse '{{begin {x <- 3} {+ x y}}
                                   where {[[x : str] := "a"] [[y : num] := 2]}}) base-tenv)))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (type-check (parse '(1 if 1 else 0)) base-tenv)))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (type-check (parse '("a" if (<= 2 1) else 0)) base-tenv)))


;; Test cases for now.
(define failed '(() => 9))
(define ft '{{{[x : num]} => {+ x 1}} 17})
(define st '{{{[x : num] {y : num}} => {+ x y}} 17})
(define ab '{{{[x : num] [x : num]} => {+ x x}} 17 17})
(check-equal? (top-interp failed) "#<procedure>")
(define var '{{+ z y}
              where
              {[[z : num] := {+ 9 14}]
               [[y : num] := 98]}})
(define strs '{{str-eq? z y}
               where
               {[[z : str] := "abc"]
                [[y : str] := "abc"]}})
(define iftst '{{{+ z y} if {num-eq? z y} else {- z y}}
                where
                {[[z : num] := 10]
                 [[y : num] := 10]}})
(define iftst2 '{{{+ z y} if {num-eq? z y} else {- z y}}
                 where
                 {[[z : num] := 10]
                  [[y : num] := 5]}})
(check-equal? (top-interp iftst) "20")
(check-equal? (top-interp iftst2) "5")
(check-equal? (top-interp strs) "true")
(check-equal? (serialize (closV '() (NumC 2) top-env)) "#<procedure>")
(check-equal? (serialize (primV '+)) "#<primop>")
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp st)))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse ab)))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (lookup 'abc top-env)))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '(3 4 5))))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse '(+ if 4))))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '(7 if (+ 4 3) else 8))))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '(/ 1 (- 3 3)))))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '(+ + +))))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '(+ 4 (error "1234")))))
(check-equal? (top-interp var) "121")
(check-equal? (LamC '(f g) (list (fun (list (str)) (bool)) (fun (list (num)) (str)))
                    (LamC '(x) (list (num)) (AppC (IdC 'f) (list (AppC (IdC 'g) (list (IdC 'x)))))))
              (parse '{{[f : (str -> bool)] [g : (num -> str)]} => {{[x : num]} => {f {g x}}}}))
(check-equal? (AppC (LamC '(z y) (list (num) (num))
                          (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98)))
              (parse '{{+ z y}
                       where
                       {[[z : num] := {+ 9 14}] [[y : num] := 98]}}))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse '())))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '{{+ + y}
                                   where
                                   {[[y : num] := 98]}})))

(check-equal? (top-interp '{{- z y}
                           where
                           {[[z : num] := 3]
                            [[y : num] := 2]}}) "1")
(check-equal? (top-interp '{{* z y}
                           where
                           {[[z : num] := 3]
                            [[y : num] := 2]}}) "6")
(check-equal? (top-interp '{{/ z y}
                           where
                           {[[z : num] := 2]
                            [[y : num] := 2]}}) "1")
(check-equal? (top-interp '{{num-eq? z y}
                           where
                           {[[z : num] := 3]
                            [[y : num] := 2]}}) "false")
(check-equal? (top-interp '{{str-eq? z y}
                           where
                           {[[z : str] := "a"]
                            [[y : str] := "a"]}}) "true")
(check-equal? (top-interp '{{str-eq? z y}
                           where
                           {[[z : str] := "a"]
                            [[y : str] := "b"]}}) "false")
(check-equal? (top-interp '{{substring z y x}
                            where
                            {[[z : str] := "abc"]
                             [[y : num] := 0]
                             [[x : num] := 2]}}) "ab")
(check-equal? (top-interp '{{arr x y}
                            where
                            {[[y : num] := 3]
                             [[x : num] := 4]}}) "#<array>")
(check-equal? (top-interp '{{aref {makearr 1 2 3} x}
                            where
                            {[[x : num] := 1]}}) "2")
(check-equal? (top-interp '{{aset {makearr 1 2 3} x y}
                            where
                            {[[x : num] := 1]
                             [[y : num] := 4]}}) "#<void>")
(check-equal? (top-interp '{alen {makearr 1 2 3}}) "3")
(check-equal? (interp #t top-env) (boolV #t))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (top-interp '{alen {makearr 1.2 2 3}})))
(check-equal? (top-interp '{{begin {+ x y} {x <- 3}}
                                   where {[[x : num] := 1] [[y : num] := 2]}}) "#<void>")






(check-equal? (top-interp '{letrec {square-helper {[n : num]} : num =>
                                                  {0 if {<= n 0} else {+ n {square-helper {- n 2}}}}}
                             in
                             {{square 4}
                              where
                              {[[square : {num -> num}] := {{[n : num]} => {square-helper {- {* 2 n} 1}}}]}}}) "16")
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (type-check (parse '{letrec {square-helper {[n : num]} : num =>
                                                                 {"a" if {<= n 0} else "b"}}
                                            in
                                            {{square 4}
                                             where
                                             {[[square : {num -> num}] := {{[n : num]} =>
                                             {square-helper {- {* 2 n} 1}}}]}}}) base-tenv)))

(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (type-check (parse '{letrec {square-helper {[n : num]} : str =>
                                                                 {0 if {<= n 0} else {+ n {square-helper {- n 2}}}}}
                                            in
                                            {{square 4}
                                             where
                                             {[[square : {num -> num}] := {{[n : num]} =>
                                             {square-helper {- {* 2 n} 1}}}]}}}) base-tenv)))

(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse '{letrec {square-helper {[if : num]} : num =>
                                                     {0 if {<= n 0} else {+ n {square-helper {- n 2}}}}}
                                in
                                {{square 4}
                                 where
                                 {[[square : {num -> num}] := {{[n : num]} => {square-helper {- {* 2 n} 1}}}]}}})))
(check-exn (regexp (regexp-quote "VVQS"))
           (lambda () (parse '{letrec {square-helper {[a : num] [a : num]} : num =>
                                                     {0 if {<= n 0} else {+ n {square-helper {- n 2}}}}}
                                in
                                {{square 4}
                                 where
                                 {[[square : {num -> num}] := {{[n : num]} => {square-helper {- {* 2 n} 1}}}]}}})))




