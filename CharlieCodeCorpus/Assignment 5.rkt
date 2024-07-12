#lang typed/racket
(require typed/rackunit)

; Implemented full project

; Defines a new language ZODE with as per the spec
(define-type ExprC (U numC ifC idC appC lambC strC))
(struct numC ([n : Real]) #:transparent)
(struct strC ([s : String]) #:transparent)
(struct ifC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct idC ([name : Symbol]) #:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct lambC ([arglst : (Listof Symbol)] [body : ExprC]) #:transparent)

; Defines the types of values that ZODE expects
(define-type Value (U Real Boolean String closV Primop))
(struct closV ([arglst : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)

; Defines the primitive operators built into ZODE
(define-type Primop (U primop-numeric primop-bool primop-error
                       primop-println primop-read-num primop-read-str primop-seq primop-plusplus))
(struct primop-numeric ([name : Symbol]) #:transparent)
(struct primop-bool ([name : Symbol]) #:transparent)
(struct primop-error ([name : Symbol]) #:transparent)
(struct primop-println ([name : Symbol]) #:transparent)
(struct primop-read-num ([name : Symbol]) #:transparent)
(struct primop-read-str ([name : Symbol])  #:transparent)
(struct primop-seq ([name : Symbol])  #:transparent)
(struct primop-plusplus ([name : Symbol])  #:transparent)


; Defines the environment datastructure
(define-type Env (Listof Binding))
(struct Binding ([name : Symbol] [val : Value]))
; binds top level definitions
(define mt-env (list
                (Binding 'true #t)
                (Binding 'false #f)
                (Binding '+ (primop-numeric '+))
                (Binding '- (primop-numeric '-))
                (Binding '* (primop-numeric '*))
                (Binding '/ (primop-numeric '/))
                (Binding '<= (primop-numeric '<=))
                (Binding 'equal? (primop-bool 'equal?))
                (Binding 'error (primop-error 'error))
                (Binding 'println (primop-println 'println))
                (Binding 'read-num (primop-read-num 'read-num))
                (Binding 'read-str (primop-read-str 'read-str))
                (Binding 'seq (primop-seq 'seq))
                (Binding '++ (primop-plusplus '++))))

; Serializes a ZODE 4 expression
(define (serialize [val : Value]) : String
  (match val
    [(? real? n) (format "~v" n)]
    [(? boolean? b) (if b "true" "false")]
    [(? closV? closure) "#<procedure>"]
    [(? primop-numeric? prim) "#<primop>"]
    [(? primop-error? err) "#<primop>"]
    [(? primop-bool? prim) "#<primop>"]
    [(? primop-println? prim) "#<primop>"]
    [(? primop-read-num? prim) "#<primop>"]
    [(? primop-read-str? prim) "#<primop>"]
    [(? primop-seq? prim) "#<primop>"]
    [(? primop-plusplus? prim) "#<primop>"]
    [(? string? s) (format "~v" s)]))

; Accepts an s-expression in the ZODE language and evaluates it, serializing the result
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) mt-env)))

; Accepts an s-expression and parses it into an ZODE expression
(define (parse [s : Sexp]) : ExprC
  (match s
    [(list 'locals ': args ...) (parse (desugar args))]
    [(list 'lamb ': vars ... ': body)
     (define varlist (get-symbols vars))
     (cond
       [(duplicate-args? varlist) (error 'parse "ZODE Duplicate variable names")]
       [(invalid-params? varlist) (error 'parse "ZODE Can't use keywords as variable names")]
       [else (lambC varlist (parse body))])]
    [(list (? list? body) args ...)
     (appC (parse body) (map parse args))]
    [(list 'if ': test ': then ': else) (ifC (parse test) (parse then) (parse else))]
    [(list firstval args ...) (appC (parse firstval) (map parse args))]
    [(? symbol? arg)
     (cond
       [(invalid-params? (list arg)) (error 'parse "ZODE Can't use keywords as variable names")]
       [else (idC arg)])]
    [(? real? n) (numC n)]
    [(? string? s) (strC s)]))

; Accepts a ZODE4 expression and interprets it
(define (interp [a : ExprC] [env : Env]) : Value
  (match a
    [(numC n) n]
    [(strC s) s]
    [(appC fun args)
     (define fun-val (interp fun env))
     (cond
       [(primop-numeric? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (define cleaned-args (clean-primparams processed-args))
        (cond
          [(not (equal? (length cleaned-args) 2))
           (error 'interp "ZODE Invalid args for binop")]
          [else (define left (first cleaned-args))
                (define right (first (rest cleaned-args)))
                (match (primop-numeric-name fun-val)
                  ['+ (+ left right)]
                  ['- (- left right)]
                  ['* (* left right)]
                  ['/
                   (if (equal? right 0)
                       (error 'interp "ZODE Divide by 0 error")
                       (/ left right))]
                  ['<= (<= left right)]
                  )])]
       [(primop-bool? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (equal? (first processed-args) (first (rest processed-args)))]
       [(primop-error? fun-val)
        (error 'interp "user-error ~s" (map (lambda ([arg : ExprC]) : String (serialize (interp arg env))) args))]
       [(primop-println? fun-val)
        (cond
              [(not (equal? (length args) 1))
               (error 'interp "ZODE Invalid arguments for println")]
              [else
               (define firstarg (first args))
               (printf (serialize (interp firstarg env)))
               (newline)
               #t])]
       [(primop-read-num? fun-val)
        (displayln ">")
        (define read-value (read-line))
        (cond
          [(eof-object? read-value)
               (error 'interp "ZODE user passed in EOF to read-num")]
          [(not (string? read-value))
           (error 'interp "ZODE user passed in non string to read-num (pre-parse)")]
          [else
           (define numeric-value (string->number read-value))
           (cond
             [(not (real? numeric-value))
              (error 'interp "ZODE user passed in non real to read-num")]
             [else
              numeric-value])])]
       [(primop-read-str? fun-val)
        (displayln ">")
        (define read-value (read-line))
        (cond
          [(eof-object? read-value) ""]
          [else read-value])]
       [(primop-seq? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (get-last processed-args)]
       [(primop-plusplus? fun-val)
        (define processed-args (map (lambda ([arg : ExprC]) : Value (interp arg env)) args))
        (append-multi-str processed-args)]
       [(closV? fun-val)
        (define bindings
          (zip (closV-arglst (cast fun-val closV))
               (map
                (lambda ([arg : ExprC]) : Value (interp arg env))
                args)))
        (define extended-env (extend-env bindings (closV-env fun-val)))
        (interp (closV-body fun-val) extended-env)]
       [else
        (error 'interp "ZODE function did not eval to closure ~s" fun)])]
    [(lambC args body)
     (closV args body env)]
    [(ifC test then else)
     (define result (interp test env))
     (if (not (boolean? result))
         (error 'interp "ZODE if test non-boolean")
         (if result (interp then env) (interp else env)))]
    [(idC val) (lookup val env)]))

; looks up an identifier in the environment and returns the value
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "ZODE Unbound identifier ~s" for)]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (Binding-val (first env))]
            [else (lookup for (rest env))])]))

; Zips two lists together
(define (zip [what : (Listof Symbol)] [to : (Listof Value)]) : (Listof Binding)
  (match (list what to)
    [(list '() '()) '()]
    [(list (cons f-what r-what) '()) (error 'zip "ZODE Invalid number of params")]
    [(list '() (cons f-to r-to)) (error 'zip "ZODE Invalid number of params")]
    [(list (cons f-what r-what) (cons f-to r-to)) (cons (Binding f-what f-to) (zip r-what r-to))]))

; Gets the last value in a list
(define (get-last [lst : (Listof Value)]) : Value
  (cond
    [(empty? (rest lst))
     (first lst)]
    [else
     (get-last (rest lst))]))

; Appends a list of strings together, ensuring all passed in args are actually strings
(define (append-multi-str [lst : (Listof Value)]) : String
  (cond
    [(empty? lst)
     ""]
    [else
     (string-append (stringify (first lst)) (append-multi-str (rest lst)))]))

; Takes a value and "stringifies it"
(define (stringify [val : Value]) : String
  (cond
    [(string? val) val]
    [(real? val) (number->string val)]
    [else
     (error 'stringify "ZODE Un-interpretable value passed into ++")]))

; Binds multiple params to their values, replacing old bindings if they have the same name
(define (extend-env [bindings : (Listof Binding)] [env : Env]) : Env
  (cond
    [(empty? bindings)
     env]
    [(empty? env)
     (cons (first bindings) (extend-env (rest bindings) env))]
    [else
     (define first-env (first env))
     (define first-bind (first bindings))
     (cond
       [(symbol=? (Binding-name first-env) (Binding-name first-bind))
        (cons first-bind (extend-env (rest bindings) env))]
       [else
        (cons first-env (extend-env bindings (rest env)))])]))

; Cleans primitive params, looks for only numeric
(define (clean-primparams [params : (Listof Value)]) : (Listof Real)
  (cond
    [(empty? params) '()]
    [(not (real? (first params)))
      (error 'clean-primparams "ZODE Invalid param for numeric primitive ~s" (first params))]
    [else
     (cons (cast (first params) Real) (clean-primparams (rest params)))]
    ))

; Determines if there are duplicate arguments
(define (duplicate-args? [args : (Listof Symbol)]) : Boolean
  (cond
     [(empty? args) #f] 
     [(not (not (member (first args) (rest args)))) #t]
     [else (duplicate-args? (rest args))]))

; Determines if keywors are being used as params
(define (invalid-params? [args : (Listof Symbol)]) : Boolean
  (cond
    [(empty? args) #f]
    [(or (symbol=? (first args) 'locals)
         (symbol=? (first args) 'if)
         (symbol=? (first args) 'lamb)
         (symbol=? (first args) ':)
         (symbol=? (first args) '=)) #t]
    [else (invalid-params? (rest args))]))

; Grabs the symbols from a list of parameters,
; signals error if encounters non symbol
(define (get-symbols [args : (Listof Any)]) : (Listof Symbol)
  (cond
    [(empty? args) '()]
    [(not (symbol? (first args)))
     (error 'get-symbols "ZODE Vars not entierly symbols")]
    [else (cons (first args) (get-symbols (rest args)))]))

; Desugars, splits the locals definitions into the variables, the body of the main lamb, and the bodies of the
; Arguments to be passed into the variables
(define (split-desugar [s : Sexp] [vars : (Listof Symbol)] [bodies : (Listof Sexp)]) : (Listof Sexp)
  (match s
    [(list (? symbol? varname) '= args ': rest ...)
     (split-desugar rest (append vars (list varname)) (append bodies (list args)))]
    [(list body) (list vars bodies body)]
    [else (error 'split-desugar "ZODE Invalid locals definition")]))

; Desugars, wraps the main lamb into external lambs
(define (desugar [args : Sexp]) : Sexp
  (define desugar-results (split-desugar args '() '()))
  (define vars (first desugar-results))
  (define bodies (first (rest desugar-results)))
  (define body (first (rest (rest desugar-results))))
  (define varslist (cast vars (Listof Any)))
  (define bodieslist (cast bodies (Listof Any)))
  (cast (append (list (append (list 'lamb ':) varslist (list ':) (list body))) bodieslist) Sexp))

; Interp Tests
(check-equal? (interp (appC (idC '+) (list (numC 3) (numC 5))) mt-env) 8)
(check-equal? (interp (appC (idC '*) (list (numC 3) (numC 5))) mt-env) 15)
(check-equal? (interp (appC (idC '<=) (list (numC 3) (numC 5))) mt-env) #t)
(check-equal? (interp (appC (idC '<=) (list (numC 8) (numC 5))) mt-env) #f)
(check-equal? (interp (appC (idC 'equal?) (list (numC 8) (numC 8))) mt-env) #t)
(check-equal? (interp (appC (idC 'equal?) (list (numC 8) (numC 2))) mt-env) #f)
(check-equal? (interp (appC (idC 'equal?) (list (idC 'false) (idC 'true))) mt-env) #f)
(check-equal? (interp (appC (idC '+) (list (appC (idC '*) (list (numC 2) (numC 4))) (numC 5))) mt-env) 13)
(check-equal? (interp (ifC (appC (idC '<=) (list (numC 4) (numC 0))) (idC 'true) (idC 'false)) mt-env) #f)
(check-equal? (interp (ifC (appC (idC '<=) (list (numC 3) (numC 4))) (numC 3) (numC 4)) mt-env) 3)
(check-equal? (interp (appC (idC '+) (list
                                      (numC 3)
                                      (appC (lambC '(x)
                                                   (appC (idC '+) (list (idC 'x) (idC 'x))))
                                            (list (numC 3))))) mt-env) 9)
(check-exn (regexp (regexp-quote "ZODE Unbound identifier"))
           (lambda () (interp (appC (idC '+) (list (numC 4) (idC 'x))) mt-env)))

(check-exn (regexp (regexp-quote "ZODE Invalid number of params"))
           (lambda () (interp
                       (appC (lambC (list 'x) (appC (idC '+) (list (numC 1) (idC 'x))))
                             (list (numC 1) (numC 2))) mt-env)))
(check-exn (regexp (regexp-quote "ZODE Invalid number of params"))
           (lambda () (interp
                       (appC (lambC (list 'x 'y 'z) (appC (idC '+) (list (numC 1) (idC 'x))))
                             (list (numC 1) (numC 2))) mt-env)))

; Parser Tests
(check-equal? (parse
               '{locals
                 : z = {+ 9 14}
                 : y = 98
                 : {+ z y}})
              (appC (lambC (list 'z 'y) (appC (idC '+) (list (idC 'z) (idC 'y))))
                    (list (appC (idC '+) (list (numC 9) (numC 14))) (numC 98))))
(check-equal? (parse
               '{if : 1 : 2 : 3})
               (ifC (numC 1) (numC 2) (numC 3)))
(check-equal? (parse '{+ 1 2})
              (appC (idC '+) (list (numC 1) (numC 2))))
(check-equal? (parse 1) (numC 1))
(check-equal? (parse '{* 1 2})
              (appC (idC '*) (list (numC 1) (numC 2))))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names")) (lambda () (parse '{+ if 4})))
(check-exn (regexp (regexp-quote "ZODE Duplicate variable names")) (lambda () (parse '{lamb : x x : 1})))
(check-exn (regexp (regexp-quote "ZODE Vars not entierly symbols")) (lambda () (parse '{lamb : 1 2 3 : 5})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{lamb : i : "Hello" 31/7 +})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{lamb : locals : 1})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{foo : i : "Hello" 31/7 +})))
(check-exn (regexp (regexp-quote "ZODE Can't use keywords as variable names"))
           (lambda () (parse '{= : i : "Hello" 31/7 +})))


; Top Interp Tests
(check-equal? (top-interp '{locals
              : z = {+ 9 14}
              : y = 98
              : {+ z y}}) "121")
(check-equal? (top-interp
               '{+ 1 2})
              "3")
(check-equal? (top-interp
               '{locals
                 : x = 1
                 : y = 2
                 : {- 1 {+ x y}}}) "-2")
(check-equal? (top-interp
               '{locals
                 : x = 1
                 : y = 2
                 : {/ 3 {+ x y}}}) "1")
(check-exn (regexp (regexp-quote "ZODE Divide by 0 error")) (lambda ()(top-interp
               '{locals
                 : x = {+ 3 4}
                 : y = {/ 1 {+ 0 0}}
                 : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid param for numeric primitive"))
           (lambda () (top-interp
                       '{locals
                         : x = {+ 1 true}
                         : y = 4
                         : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         : x
                         : y = 4
                         : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         :
                         : y = 4
                         : {+ 1 2}})))
(check-exn (regexp (regexp-quote "ZODE Invalid locals definition"))
           (lambda () (top-interp
                       '{locals
                         : y = 4 x = 3
                         : 1})))
(check-equal? (top-interp
               '{locals
                 : x = 1
                 : y = 1
                 : 1}) "1")
(check-exn (regexp (regexp-quote "ZODE if test non-boolean"))
           (lambda () (top-interp
                      '{if : 1 : 2 : 3})))
(check-exn (regexp (regexp-quote "ZODE function did not eval to closure"))
           (lambda () (top-interp
                       '{locals
                         : x = 1
                         : {x 1}})))
(check-equal? (top-interp
               '+) "#<primop>")
(check-equal? (top-interp
               '{lamb : x : {+ 1 x}}) "#<procedure>")
(check-equal? (top-interp
               '{if : true : true : false}) "true")
(check-equal? (top-interp
               '{if : true : false : true}) "false")
(check-exn (regexp (regexp-quote "ZODE Invalid args for binop"))
           (lambda () (top-interp
                       '{+})))
(check-exn (regexp (regexp-quote "ZODE Invalid args for binop"))
           (lambda () (top-interp
                       '{+ 2 3 4})))
(check-equal? (top-interp
 '{{lamb : seven : {seven}}
   {{lamb : minus : {lamb : : {minus {+ 3 10} {* 2 3}}}}
    {lamb : x y : {+ x {* -1 y}}}
    }}) "7")
(check-equal? (top-interp
 '{{lamb : + : (* + +)} 14}) "196")
(check-exn (regexp (regexp-quote "ZODE function did not eval to closure"))
           (lambda () (top-interp '{3 4 5})))
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (top-interp
                       '{+ 4 {error "1234"}})))
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (top-interp '{{lamb : e : {e e}} error})))
(check-equal? (top-interp '{locals
              : x = 5
              : y = 2
              : successMSG = "Success!"
              : failMSG = "Fail!"
              : {if : {<= {+ 5 2} {* 5 2}} : successMSG : failMSG}}) "\"Success!\"")

; (check-equal? (top-interp '{locals
;                             : fact = {lamb : n self :
;                                            {if
;                                             : {equal? n 0}
;                                             : 1
;                                             : {* n {self {- n 1} self}}}}
;                             : {fact 5 fact}}) "120")

; How Do I check the "side-effects" work properly?
(check-equal? (top-interp '{println "Hello world"}) "true")
;(check-equal? (top-interp '{read-num}) "4")
;(check-equal? (top-interp '{read-str}) "\"Hello world\"")
(check-equal? (top-interp '{seq 1 2 3}) "3")
(check-equal? (top-interp '{++ "Hello " {+ 1 3} " World"}) "\"Hello 4 World\"")

; Covers serialization
(check-equal? (top-interp 'println) "#<primop>")
(check-equal? (top-interp 'read-num) "#<primop>")
(check-equal? (top-interp 'read-str) "#<primop>")
(check-equal? (top-interp 'equal?) "#<primop>")
(check-equal? (top-interp 'seq) "#<primop>")
(check-equal? (top-interp '++) "#<primop>")


; Custome Zode 5 Function
(define example-program
  '{seq {println "Welcome to 2-player rock paper scissors."}
        {locals : p1_choice = {seq {println "Player 1, enter your choice of Rock, Paper, or Scissors"} {read-str}}
                : p2_choice = {seq {println "Player 2, enter your choice of Rock, Paper, or Scissors"} {read-str}}
                : {seq
                   {println {++ "Player 1 Chose " p1_choice ", Player 2 Chose " p2_choice}}
                   {if : {equal? p1_choice p2_choice}
                       : {println {"It is a tie."}}
                       : {if : {equal? p1_choice "Rock"}
                             : {if : {equal? p2_choice "Paper"}
                                   : {println "Player 2 Wins!"}
                                   : {println "Player 1 Wins!"}}
                             : {if : {equal? p1_choice "Paper"}
                                   : {if : {equal? p2_choice "Scissors"}
                                         : {println "Player 2 Wins!"}
                                         : {println "Player 1 Wins!"}}
                                   : {if : {equal? p1_choice "Scissors"}
                                         : {if : {equal? p2_choice "Rock"}
                                               : {println "Player 2 Wins!"}
                                               : {println "Player 1 Wins!"}}
                                         : {println "Player 1 made an invalid choice,
therefore Player 2 Wins!"}}}}}}}})

;(top-interp example-program)
;(parse '{"hello world"})
;(top-interp '{"Hello world"})


; Example output
; "Welcome to 2-player rock paper scissors."
; "Player 1, enter your choice of Rock, Paper, or Scissors"
; >
; Rock
; "Player 2, enter your choice of Rock, Paper, or Scissors"
; >
; Scissors
; "Player 1 Chose Rock, Player 2 Chose Scissors"
; "Player 1 Wins!"
; "true"