;;> Maximum points for this assignment: <+100>
;;> eyeball: 5/6; some tests failed, missing while and in order

;;> Testfail: while evaluating (top-interp (quote (var (f = (new-array 5 false)) (begin (aset! f 0 19) (aset! f (+ 0 1) 20) (aset! f 0 87) (+ (* 100 (aref f 0)) (aref f 1)))))):
;  multiply: RGME: Non number multiplication
;;> Testfail: expected exception with message containing RGME on test expression: '(top-interp '(var (f = (new-array 5 false)) (aset! f -1 19)))
;;> Testfail: while evaluating (top-interp (quote (var (a = 9) (b = (array 3 false true 19)) (d = (array "otter")) (var (c = (lam () (begin (aset! d 0 b) (aset! b 3 333) (+ (aref (aref d 0) 3) a)))) (c))))):
;  aref: RGME: Cannot Reference Non-array
;;> Testfail: while evaluating (top-interp (quote (var (a = (array 0)) (var (a! = (lam (expected) (if (equal? (aref a 0) expected) (begin (aset! a 0 (+ 1 (aref a 0))) 273) (/ 1 0)))) (begin (+ (a! 0) (a! 1)) (if (begin (a! 2) true) (a! 3) (/ 1 0)) (new-array (begin (a! 4) 34) (begin (a! 5) false)) (aset! (begin (a! 6) (new-array 3 false)) (begin (a! 7) 2) (begin (a! 8) 98723)) (var (p = 9) (p <- (a! 9))) ((begin (a! 10) (lam (x y) (begin (a! 13) (+ x y)))) (begin (a! 11) 3) (begin (a! 12) 4)) (var (a = (a! 14)) (b = (a! 15)) (a! 16)) (a! 17) 14))))):
;  divide: RGME: Invalid Division
;;> Testfail: while evaluating (top-interp (quote (var (halt = 1) (memory = (new-array 1000 0)) (pc = (array 0)) (incr = (lam (arr) (aset! arr 0 (+ 1 (aref arr 0))))) (var (go = (var (go = (array 3735928559)) (begin (aset! go 0 (lam () (var (opcode = (aref memory (aref pc 0))) (if (equal? opcode 0) (begin (incr pc) ((aref go 0))) (if (equal? opcode 1) (aref pc 0) (/ 1 0)))))) go))) (begin (aset! memory 453 halt) ((aref go 0))))))):
;  interp: RGME: AppC - Bad Syntax
;;> Testfail: while evaluating (top-interp (quasiquote (var (while = (unquote while)) (var (in-order = (unquote in-order)) (+ (if (in-order (array 3 6 8) 3) 1 0) (if (in-order (array 6 7 3 8) 4) 0 2)))))):
;  env-lookup: RGME: Name not found

#lang typed/racket

(require typed/rackunit)
(require racket/match)


; In progress implementation of the RGME4 programming language.
; I don't have the while and in order implemented.
; I am removing all my not fully working parts so I can be able the handin something successfully.


(define while '{TODO LATER, I didn't have enough time to figure it out })
(define in-order '{TODO LATER,I didn't have enough time to figure it out})

;define Store and Location
(define-type Location Integer)
(define-type Store (Immutable-HashTable Location Value))


;define ExprC type for RGME4
(define-type ExprC (U NumC IdC AppC LamC IfC StringC SetC SeqC))

;define each struct that compose ExprC
(struct NumC ([n : Real])#:transparent)
(struct IdC ([s : Symbol])#:transparent)
(struct StringC ([s : String])#:transparent)
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)])#:transparent)
(struct LamC ([param : (Listof Symbol)] [body : ExprC])#:transparent)
(struct IfC ([aTest : ExprC][aThen : ExprC][anElse : ExprC])#:transparent)

;added for RGME4
(struct SetC([var : Symbol] [arg : ExprC])#:transparent)
(struct SeqC([exp : (Listof ExprC)] )#:transparent)

;define Value type for RGME4
(define-type Value (U NumV CloV PrimV Prim2V Prim3V Prim4V BoolV StringV NullV ArrayV ))

;define each structure that compose Value
(struct NumV ([n : Real])#:transparent)
(struct BoolV ([bool : Boolean])#:transparent)
(struct StringV ([s : String])#:transparent)
(struct CloV ([param : (Listof Symbol)] [body : ExprC] [env : Env])#:transparent)
(struct PrimV ([op : (-> Value Value Value)])#:transparent)

;Added for A4
(struct Prim2V ([op : (-> Value Value Value Value)])#:transparent)
(struct Prim3V ([op : (-> (Listof Value) Value)])#:transparent)
(struct Prim4V ([op : (-> (Listof V*S) Store)])#:transparent)
(struct NullV ([nill : Null])#:transparent)
(struct ArrayV ([size : Natural][store : Store])#:transparent)

(define invalidArguments (make-immutable-hash
                          (list (cons 'if 0)
                                (cons 'var 0)
                                (cons 'lam 0)
                                (cons '= 0)
                                (cons '<- 0))))


;define binding
(struct Binding ([name : Symbol] [location : Location])#:transparent)

(define-type Env (Listof Binding))
(define empty-env '())
(define extend-env cons)
(define empty-sto (make-immutable-hash'()))

; define Result
(define-type Result V*S)
(struct V*S ([val : Value][store : Store])#:transparent)

; add function, takes two reals and return a real
(define (add [left : Value] [right : Value]) : Value
  (cond
    [(and (NumV? left) (NumV? right))(NumV (+ (NumV-n left) (NumV-n right)))]
    [else (error 'add "RGME: Non number addition")]))

;test cases for add
(check-equal? (add (NumV 3)(NumV 4))(NumV 7))
(check-exn (regexp (regexp-quote "RGME: Non number addition"))
           (lambda ()(add (NumV 5)(BoolV #f))))
(check-exn (regexp (regexp-quote "RGME: Non number addition"))
           (lambda ()(add (StringV "Simo")(NumV 5))))

;subtract takes two reals and return a real
(define (subtract [left : Value] [right : Value]) : Value
  (cond
    [(and (NumV? left) (NumV? right))(NumV (- (NumV-n left) (NumV-n right)))]
    [else (error 'subtract "RGME: Non number subtraction")]))

;test cases for subtraction
(check-equal? (subtract (NumV 10)(NumV 4))(NumV 6))
(check-exn (regexp (regexp-quote "RGME: Non number subtraction"))
           (lambda ()(subtract (NumV 5)(BoolV #f))))
(check-exn (regexp (regexp-quote "RGME: Non number subtraction"))
           (lambda ()(subtract (StringV "Simo")(NumV 5))))

;multiplay function takes 2 reals and produce a real
(define (multiply [left : Value] [right : Value]) : Value
  (cond
    [(and (NumV? left) (NumV? right)) (NumV (* (NumV-n left) (NumV-n right)))]
    [else (error 'multiply "RGME: Non number multiplication")]))

;test cases for multiply
(check-equal? (multiply (NumV 10)(NumV 4))(NumV 40))
(check-exn (regexp (regexp-quote "RGME: Non number multiplication"))
           (lambda ()(multiply (NumV 5)(BoolV #f))))
(check-exn (regexp (regexp-quote "RGME: Non number multiplication"))
           (lambda ()(multiply (StringV "Simo")(NumV 5))))

;divide function takes 2 reals and produce a real
(define (divide [left : Value] [right : Value]) : Value
  (cond
    [(and (and (NumV? left) (NumV? right)) (not (eq? (NumV-n right) 0)))
     (NumV (/ (NumV-n left) (NumV-n right)))]
    [else (error 'divide "RGME: Invalid Division")]))

;test cases for divide
(check-equal? (divide (NumV 10)(NumV 5)) (NumV 2))
(check-exn (regexp (regexp-quote "RGME: Invalid Division"))
           (lambda ()(divide (NumV 5)(BoolV #f))))
(check-exn (regexp (regexp-quote "RGME: Invalid Division"))
           (lambda ()(divide (StringV "Simo")(NumV 5))))
(check-exn (regexp (regexp-quote "RGME: Invalid Division"))
           (lambda ()(divide (NumV 5)(NumV 0))))

;<= lteq? function two reals and returns a Boolean value whether or not the first value
;is less than or equal the second one.
(define (lteq? [left : Value] [right : Value]) : Value
  (cond
    [(not(and (NumV? left) (NumV? right)))
     (error 'lteq? "RGME: Non number comparison")]
    [(<= (NumV-n left) (NumV-n right)) (BoolV #t)]
    [else (BoolV #f)]))

;test cases for lteq?
(check-equal? (lteq? (NumV 5)(NumV 7))(BoolV #t))
(check-equal? (lteq? (NumV 5)(NumV 5))(BoolV #t))
(check-equal? (lteq? (NumV 10)(NumV 7))(BoolV #f))
(check-exn (regexp (regexp-quote "RGME: Non number comparison"))
           (lambda ()(lteq? (NumV 5)(StringV "Simo"))))

;equalV function takes two reals and returns a boolean value whether two values are
;equal to each other or not.
(define (equalV [left : Value] [right : Value]) : Value
  (cond
    [(or (or (PrimV? left) (PrimV? right)) (or (CloV? left) (CloV? right))) (BoolV #f)]
    [else
     (match left
       [(StringV s) (cond
                      [(and (StringV? right) (equal? (StringV-s right) s)) (BoolV #t)]
                      [else (BoolV #f)])]
       [(BoolV s) (cond
                    [(and (BoolV? right) (eq? (BoolV-bool right) s)) (BoolV #t)]
                    [else (BoolV #f)])]
       [(NumV s) (cond
                   [(and (NumV? right) (eq? (NumV-n right) s)) (BoolV #t)]
                   [else (BoolV #f)])])]))


;test cases for equalV
(check-equal? (equalV (NumV 5)(NumV 5)) (BoolV #t))
(check-equal? (equalV (NumV 4)(NumV 5)) (BoolV #f))
(check-equal? (equalV (StringV "Simo")(StringV "Simo")) (BoolV #t))
(check-equal? (equalV (StringV "Simo")(StringV "Mohamed")) (BoolV #f))
(check-equal? (equalV (BoolV #t)(BoolV #t))(BoolV #t))
(check-equal? (equalV (BoolV #f)(BoolV #f))(BoolV #t))
(check-equal? (equalV (BoolV #t)(BoolV #f))(BoolV #f))
(check-equal? (equalV (BoolV #f)(BoolV #t))(BoolV #f))
(check-equal? (equalV (PrimV add)(BoolV #f))(BoolV #f))
(check-equal? (equalV (PrimV multiply)(BoolV #f))(BoolV #f))

;;This is the allocate helper function that extends a storage the amount of values
;;in a storage
(define (assign [count : Nonnegative-Integer] [store : Store] [value : Value]) : Store
  (cond
    [(equal? 0 count) store]
    [else
     (assign (- count 1) (extend-sto store value) value)]))

;;This function takes in a value, amount of locations, and store and allocates a given amount
;;of space base on that value
(define (allocate [val : Value] [numLocations : Natural] [store : Store]) : (Pairof Location Store)
  (define baseLocation (new-location store))
  (cond
    [(equal? 0 numLocations) (error 'allocate "RGME: Not Able to Allocate an Empty Array")]
    [else (cons baseLocation (assign numLocations store val))]))


;;This function takes in a String Value, and two Num Values and returns the substring
(define (My-substring [str : Value] [left : Value] [right : Value]) : Value
  (cond
    [(and (StringV? str) (NumV? left) (NumV? right))
     (define l (NumV-n left))
     (define r (NumV-n right))
     (define longString (StringV-s (cast str StringV)))
     (cond
       [(or (> l r)(> r (string-length longString)))(error "RGME: Bad Indeces for substring")]
       [(and (natural? l) (natural? r))
        (StringV (substring (StringV-s str) l r))]
       [else (error 'My-substring "RGME: Only Positive Values are Accepted")])]
    [else (error 'My-substring "RGME: Invalid Arguments for Substring")]))


;test cases for My-subsring
(check-equal? (My-substring (StringV "mohamed aichouri") (NumV 0) (NumV 10)) (StringV "mohamed ai"))
(check-equal? (My-substring (StringV "abcd") (NumV 1) (NumV 3)) (StringV "bc"))
(check-exn (regexp (regexp-quote   "RGME: Invalid Arguments for Substring"))
           (lambda () (My-substring (NumV 7) (BoolV #t) (BoolV #f))))
(check-exn (regexp (regexp-quote   "RGME: Only Positive Values are Accepted"))
           (lambda () (My-substring (StringV "AichouriMohamed") (NumV -333) (NumV -33))))
(check-exn (regexp (regexp-quote   "RGME: Bad Indeces for substring"))
           (lambda () (My-substring (StringV "AichouriMohamed") (NumV 5) (NumV 1))))

;helper for my-array to take a list of values and return an array
(define (arraySet [args : (Listof Value)] [store : Store]) : Store
  (cond
    [(empty? args) store]
    [else
     (define newStore (allocate (first args) 1 store))
     (arraySet (rest args) (cdr newStore))]))

;;This function takes in a list of Values and returns an array
(define (my_array [vals : (Listof Value)]) : Value
  (ArrayV (length vals) (arraySet vals empty-sto)))


;;This function takes in a two values and allocates an array with the size of the
;;first argument and each element of the array assigned the value of the second
(define (new-array [size : Value] [value : Value]) : Value
  (match size
    [(NumV s) (cond
                [(natural? s)
                 (define newSet(allocate value s empty-sto))
                 (ArrayV s (cdr newSet))]
                [else (error 'new-array "RGME: Cannot allocate negative/zero sized array")])]
    [else (error 'new-array "RGME: Invalid Argument")]))


;aref takes in an array value and an index and returns the value at the index
(define (aref [array : Value][index : Value]) : Value
  (match array
    [(ArrayV size storage)
     (match index
       [(NumV ndx) (cond
                     [(and (natural? (+ 1 ndx)) (>= size (+ 1 ndx)))
                      (hash-ref storage (+ 1 ndx))]
                     [else (error 'aref "RGME: Reference Does not Exist")])]
       [else (error 'aref "RGME: Array Index must be number")])]
    [else (error 'aref "RGME: Cannot Reference Non-array")]))


; Updates the value at a location
(define (update [location : Location] [val : Value] [store : Store]) : Store
  (hash-set store location val))
;aset! takes an array and a value and index and puts that values in the index of the array
(define (aset! [array : Value] [index : Value] [val : Value]) : NullV
  (match array
    [(ArrayV size store)
     (match index
       [(NumV i)
        (define indexLocation (+ 1 i))
        (cond
          [(and (natural? indexLocation) (>= size indexLocation))
           (define p (update indexLocation val store))
           (NullV null)]
          [else (error 'aset! "RGME Array index out of bound")])]
       [else (error 'aset! "RGME Cannot index a non number")])]
    [else (error 'aset! "RGME Cannot call aset! on a non-array value")]))

;test cases for aset!
(check-equal? (aset! (ArrayV 3 (make-immutable-hash (list (cons 1 (NumV 1))
                                                          (cons 2 (NumV 2))
                                                          (cons 3 (NumV 3)))))
                     (NumV 0)
                     (NumV 100)) (NullV null))
(check-exn (regexp (regexp-quote "RGME Array index out of bound"))
           (lambda () (aset! (ArrayV 3 (make-immutable-hash (list (cons 1 (NumV 1))
                                                                  (cons 2 (NumV 2))
                                                                  (cons 3 (NumV 3)))))
                             (NumV 4) (NumV 100))))
(check-exn (regexp (regexp-quote "RGME Cannot index a non number"))
           (lambda () (aset! (ArrayV 3 (make-immutable-hash (list (cons 1 (NumV 1))
                                                                  (cons 2 (NumV 2))
                                                                  (cons 3 (NumV 3)))))
                             (StringV "l") (NumV 100))))
(check-exn (regexp (regexp-quote "RGME Cannot call aset! on a non-array value"))
           (lambda () (aset! (StringV "l") (NumV 0) (NumV 100))))

;myBegin takes a list of result (v*s) and returns the last one
;;> Begin still needs to evaluate EVERY item in the list: it only RETURNS the result of the last expression
(define (myBegin [list : (Listof Result)][sto : Store]): Result
  (cond
    [(empty? list)(error 'myBegin "RGME: empty body in begin")]
    [else (last list)]))

;define a global environment
(define top-env (list (Binding '+ 1)
                      (Binding '- 2)
                      (Binding '* 3)
                      (Binding '/ 4)
                      (Binding '<= 5)
                      (Binding 'equal? 6)
                      (Binding 'true 7)
                      (Binding 'false 8)
                      (Binding 'null' 9)
                      (Binding 'substring 10)
                      (Binding 'array 11)
                      (Binding 'new-array 12)
                      (Binding 'aref 13)
                      (Binding 'aset! 14)
                      ;(Binding 'begin 15)
                      ))

(define top-sto(make-immutable-hash(list (cons 1 (PrimV add))
                                         (cons 2 (PrimV subtract))
                                         (cons 3 (PrimV multiply))
                                         (cons 4 (PrimV divide))
                                         (cons 5 (PrimV lteq?))
                                         (cons 6 (PrimV equalV))
                                         (cons 7 (BoolV #t))
                                         (cons 8 (BoolV #f))
                                         (cons 9 (NullV null))
                                         (cons 10 (Prim2V My-substring))
                                         (cons 11 (Prim3V my_array))
                                         (cons 12 (PrimV new-array))
                                         (cons 13 (PrimV aref))
                                         (cons 14 (Prim2V aset!)))
                                   ;(cons 15 (Prim4V myBegin))
                                   ))

;test cases for MyBegin
(check-exn (regexp (regexp-quote "RGME: empty body in begin"))
           (lambda () (myBegin '() top-sto)))
(check-equal? (myBegin (cons (V*S (NumV 7) top-sto)(cons (V*S (NumV 5) top-sto) '())) top-sto)
              (V*S
               (NumV 5)(hash 1 (PrimV add)
                             2 (PrimV subtract)
                             3 (PrimV multiply)
                             4 (PrimV divide)
                             5 (PrimV lteq?)
                             6 (PrimV equalV)
                             7 (BoolV #t)
                             8 (BoolV #f)
                             9 (NullV '())
                             10 (Prim2V My-substring)
                             11 (Prim3V my_array)
                             12 (PrimV new-array)
                             13 (PrimV aref)
                             14 (Prim2V aset!))))

;new location takes a store and produce the next available location for the store
(define (new-location [store : Store]) : Location
  (+ 1 (hash-count store)))

;test case for new-location
(check-equal? (new-location top-sto) 15)


;extend-sto takes a store, a new location and a value. returns a new store
(define (extend-sto [sto : Store][val : Value]) : Store
  (make-immutable-hash(cons (cons (new-location sto) val) (hash->list sto))))

;store-fetch takes a location and storage and returns the value referenced at that location.
(define (store-fetch [location : Location][store : Store]) : Value
  (hash-ref store location))

;test case for store-fetch
(check-equal? (store-fetch 4 top-sto) (PrimV divide))


;change-val takes a value, store and a location and change value currently at the store to this new value
(define (changeVal [location : Location] [val : Value] [store : Store]) : Store
  (hash-set store location val))

;Test for allocate, assign, extend-sto, and new-location functions
(check-exn (regexp (regexp-quote  "RGME: Not Able to Allocate an Empty Array"))
           (lambda () (allocate (NumV 4) 0 top-sto)))
(check-equal? (allocate (NumV 2) 3 top-sto)
              (cons 15 (make-immutable-hash(list (cons 1 (PrimV add))
                                                 (cons 2 (PrimV subtract))
                                                 (cons 3 (PrimV multiply))
                                                 (cons 4 (PrimV divide))
                                                 (cons 5 (PrimV lteq?))
                                                 (cons 6 (PrimV equalV))
                                                 (cons 7 (BoolV #t))
                                                 (cons 8 (BoolV #f))
                                                 (cons 9 (NullV null))
                                                 (cons 10 (Prim2V My-substring))
                                                 (cons 11 (Prim3V my_array))
                                                 (cons 12 (PrimV new-array))
                                                 (cons 13 (PrimV aref))
                                                 (cons 14 (Prim2V aset!))
                                                 (cons 15 (NumV 2))
                                                 (cons 16 (NumV 2))
                                                 (cons 17 (NumV 2))))))

;test cases for new-array, aref functions
(check-equal? (new-array (NumV 5) (NumV 0.0))
              (ArrayV 5 (make-immutable-hash(list (cons 1 (NumV 0.0))
                                                  (cons 2 (NumV 0.0))
                                                  (cons 3 (NumV 0.0))
                                                  (cons 4 (NumV 0.0))
                                                  (cons 5 (NumV 0.0))))))
(check-exn (regexp (regexp-quote "RGME: Cannot allocate negative/zero sized array"))
           (lambda () (new-array (NumV -2) (NumV 0.0))))
(check-exn (regexp (regexp-quote "RGME: Invalid Argument"))
           (lambda () (new-array (BoolV #t) (NumV 0.0))))

(check-equal? (aref (ArrayV 7 (make-immutable-hash(list (cons 1 (NumV 3))
                                                        (cons 2 (NumV 2))
                                                        (cons 3 (NumV 10))
                                                        (cons 4 (NumV 12))
                                                        (cons 5 (NumV 0.0))
                                                        (cons 6 (NumV 7))
                                                        (cons 7 (NumV 1)))))
                    (NumV 3)) (NumV 12))
(check-exn (regexp (regexp-quote "RGME: Cannot Reference Non-array"))
           (lambda () (aref (BoolV #t) (NumV 3))))
(check-exn (regexp (regexp-quote "RGME: Array Index must be number"))
           (lambda () (aref (ArrayV 3 (make-immutable-hash(list (cons 1 (NumV 1))
                                                                (cons 2 (NumV 8))
                                                                (cons 3 (NumV 0.0))))) (StringV ""))))
(check-exn (regexp (regexp-quote "RGME: Reference Does not Exist"))
           (lambda () (aref (ArrayV 3 (make-immutable-hash(list (cons 1 (NumV 1))
                                                                (cons 2 (NumV 8))
                                                                (cons 3 (NumV 0.0))))) (NumV 10))))
(check-exn (regexp (regexp-quote "RGME: Reference Does not Exist"))
           (lambda () (aref (ArrayV 3 (make-immutable-hash(list (cons 1 (NumV 3))
                                                                (cons 2 (NumV 2))
                                                                (cons 3 (NumV 0.0))))) (NumV -10))))


;;This function takes a value and returns a string base on the Value type
(define (serialize [value : Value]) : String
  (match value
    [(NumV n) (~v n)]
    [(BoolV bool) (cond
                    [bool "true"]
                    [else "false"])]
    [(StringV str) (~v str)]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]
    [(ArrayV _ _) "#<array>"]))

;test case for serialize
(check-equal? (serialize (NumV 34)) "34")
(check-equal? (serialize (StringV "simo"))"\"simo\"")
(check-equal? (serialize (BoolV true))"true")
(check-equal? (serialize (BoolV false)) "false")
(check-equal? (serialize (CloV (list 'l)(NumC 3) top-env))"#<procedure>")
(check-equal? (serialize (PrimV multiply))"#<primop>")
(check-equal? (serialize (ArrayV 3 (make-immutable-hash(list (cons 1 (NumV 3))
                                                             (cons 2 (NumV 2))
                                                             (cons 3 (NumV 9.0))))))
              "#<array>")

;updated env-lookup for A4
;env-lookup takes a symbol and an environment and returns a binding value for the symbol
;if exits, otherwise, it raises an error.
;form lecture notes : (IdC name) (env-lookup name env)
(define (env-lookup [for : Symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'env-lookup "RGME: Name not found")]
    [else (cond
            [(symbol=? for (Binding-name (first env)))
             (Binding-location (first env))]
            [else (env-lookup for (rest env))])]))

(define testEnv '())
;test cases for env-lookup function
(check-exn (regexp (regexp-quote  "RGME: Name not found"))
           (lambda () (env-lookup '>= top-env)))
(check-equal? (env-lookup '+ top-env) 1)
(check-equal? (env-lookup 'true top-env) 7)
(check-exn (regexp (regexp-quote "RGME: Name not found"))
           (lambda ()(env-lookup 'simo top-env)))
(check-exn (regexp (regexp-quote "RGME: Name not found"))
           (lambda ()(env-lookup 'simo testEnv)))


;envList-extend takes an old environment, listof Symbols and list of Value
;and extend the old env to contain new binding. this is a helper for interp.
(define (envList-extend [params : (Listof Symbol)] [argLocations : (Listof (Pairof Location Store))][env : Env]) : Env
  (cond
    [(not(eq? (length params) (length argLocations))) (error 'envList-extend "RGME: Invalid Number of Args")]
    [(empty? params) env]
    [else
     (append (list (Binding (first params) (car (first argLocations))))
             (envList-extend (rest params) (rest argLocations) env))]))

;test cases for envList-extend.
(check-exn (regexp (regexp-quote  "RGME: Invalid Number of Args"))
           (lambda () (envList-extend (list 'a 'c 'd) (list (cons 19 top-sto)) top-env)))

;;This function takes in a an extended environment and a storage and extends the storage to account
;;for new environment variables
(define (stoList-extend [args : (Listof Value)] [store : Store]) : (Listof (Pairof Location Store))
  (cond
    [(empty? args) '()]
    [else
     (define newStore (allocate (first args) 1 store))
     (append (list newStore) (stoList-extend (rest args) (cdr newStore)))]))


;multiInterp takes a list of ExprC, and Env and Store. return a list of Result
(define (multiInterp [exps : (Listof ExprC)][env : Env][sto : Store]) : (Listof Result)
  (cond
    [(empty? exps) '()]
    [else
     (define res (interp (first exps) env sto))
     (match res
       [(V*S val res-sto)
        (cons res (multiInterp (rest exps) env res-sto))])]))

;interp function takes and ExprC, an Env and return a number value
(define (interp [exp : ExprC] [env : Env][sto : Store]) : Result
  (match exp
    [(NumC n) (V*S (NumV n) sto)]
    [(StringC str) (V*S (StringV str) sto)]
    [(IfC i t e) (define condition (interp i env sto))
                 (match condition
                   [(V*S (? BoolV? value) nSto) (cond
                                                  [(BoolV-bool value) (interp t env nSto)]
                                                  [else (interp e env nSto)])]
                   [else (error 'interp "RGME: Non Conditional Statement Passed")])]
    [(AppC func args) (let*
                          ([f-value (interp func env sto)]
                           [argRes (multiInterp args env (V*S-store f-value))]
                           [argVals (map (lambda ([x : Result])(V*S-val x)) argRes)]
                           [lastStor (cond
                                       [(empty? argRes) (V*S-store f-value)]
                                       [else (V*S-store (last argRes))])])
                        (match f-value
                          [(V*S (? CloV? clo-val) _)
                           (match clo-val
                             [(CloV param body clo-env)
                              (define locStoPair (stoList-extend argVals lastStor))
                              (define env2 (envList-extend param locStoPair clo-env))
                              (define newSto (cond
                                               [(empty? locStoPair) lastStor]
                                               [else (cdr (last locStoPair))]))
                              (interp body env2 newSto)])]
                          [(V*S (? PrimV? op) _)(V*S ((PrimV-op op) (first argVals) (second argVals)) lastStor)]
                          [(V*S (? Prim2V? op) _)
                           (V*S ((Prim2V-op op) (first argVals) (second argVals) (third argVals)) lastStor)]
                          [(V*S (? Prim3V? op) _) (V*S ((Prim3V-op op) argVals) lastStor)]
                          ; [(V*S (? Prim2V f) stoUnused)
                          ;  (V*S ((Prim2V f) (first argVals) (second argVals) (third argVals)) lastStor)]
                          [else (error 'interp "RGME: AppC - Bad Syntax")]))]
    [(IdC s) (V*S (store-fetch (env-lookup s env) sto) sto)]
    [(LamC arg body) (V*S (CloV arg body env) sto)]
    [(SetC var val)
     (define res (interp val env sto))
     (match res
       [(V*S resVal resSto)
        (let*
            ([where (env-lookup var env)]
             [newStore (changeVal where resVal resSto)])
          (define results (V*S (NullV null) newStore))
          results)])]
    [(SeqC exprs)
     (SeqEvaluate exprs env sto)]))


; Helper to evaluate a list of SeqC, returning the last one
(define (SeqEvaluate [expressions : (Listof ExprC)] [env : Env] [sto : Store]) : Result
  (define res (interp (first expressions) env sto))
  (cond
    [(empty? (rest expressions)) res]
    [else (match res
            [(V*S val newSto)
             (SeqEvaluate (rest expressions) env newSto)])]))


;test cases for interp
(check-equal? (V*S-val(interp (NumC 10) top-env top-sto))(NumV 10))
(check-equal? (V*S-val(interp (StringC "Simo") top-env top-sto))(StringV "Simo"))
(check-equal? (V*S-val(interp (IfC (AppC (LamC (list 'a 'b)(AppC (IdC '<=)(list (IdC 'a)(IdC 'b))))
                                         (list (NumC 10)(NumC 100)))
                                   (NumC 20)(NumC -1)) top-env top-sto))(NumV 20))
(check-equal? (V*S-val(interp (IfC (AppC (LamC (list 'a 'b)(AppC (IdC 'equal?)(list (IdC 'a)(IdC 'b))))
                                         (list (NumC 10)(NumC 10)))
                                   (NumC 20)(NumC -1)) top-env top-sto))(NumV 20))
(check-exn (regexp (regexp-quote "RGME: Non Conditional Statement Passed"))
           (lambda ()(interp (IfC (AppC (LamC (list 'a 'b)(AppC (IdC '+)(list (IdC 'a)(IdC 'b))))
                                        (list (NumC 10)(NumC 10)))
                                  (NumC 20)(NumC -1)) top-env top-sto)))
(check-equal? (V*S-val (interp (AppC (LamC (list 'c) (IdC 'c)) (list (NumC 5))) top-env top-sto)) (NumV 5))
(check-equal? (V*S-val (interp (AppC (IdC '+) (list (NumC 4) (NumC 3))) top-env top-sto)) (NumV 7))
(check-equal? (V*S-val (interp (AppC (LamC (list 'x 'y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                                     (list (NumC 4) (NumC 5))) top-env top-sto)) (NumV 9))
(check-equal? (V*S-val (interp (IfC (AppC (LamC (list 'x 'y) (AppC (IdC '<=) (list (IdC 'x) (IdC 'y))))
                                          (list (NumC 4) (NumC 5)))
                                    (NumC 5) (NumC -5)) top-env top-sto)) (NumV 5))
(check-equal? (V*S-val (interp (IfC (AppC (LamC (list 'x 'y) (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))))
                                          (list (NumC 4) (NumC 5)))
                                    (NumC 5) (NumC -5)) top-env top-sto)) (NumV -5))
(check-equal? (V*S-val (interp (AppC (LamC '(a) (SetC 'a (NumC 0))) (list (StringC "val")))
                               top-env
                               top-sto))
              (NullV null))

(define (checkSymbols [ s : Any]): Boolean
  (hash-has-key? invalidArguments s))

;CheckSymbol helper funtion for desugar, takes a symbol and check if that symbol
;exist in the invalidArguments hashTable. return true if it exit, false otherwise.
(define (invalcheckSymbols [args : (Listof Symbol)]) : Boolean
  (cond
    [(empty? args) #f]
    [else
     (cond
       [(hash-has-key? invalidArguments (first args)) #t]
       [else (invalcheckSymbols (rest args))])]))

;desugar function takes alist of Sexp and return an ExprC. it is a helper function
;to parse that parse an Sexpr starting with var into a lam format.
(define (desugar [exprs : Sexp]) : ExprC
  (match exprs
    [(list 'var (list id '= value) ... e)
     (cond
       ;Check-duplicate returns #f only if there is no duplicats in the list
       [(check-duplicates id) (error 'parse  "RGME: Var with duplicate Args")]
       ;ormap return false only if checkSymbol returns false in every element of id list
       [(ormap checkSymbols id) (error 'parse "RGME: Illegal Id")]
       [(AppC (LamC (cast id (Listof Symbol))
                    (parse e))(map parse (cast value (Listof Sexp))))])]))


;parse function takes an Sexp and returns a parsed expression in terms of ExprC
(define (parse [expr : Sexp]) : ExprC
  (match expr
    [(? real? n) (NumC n)]
    [(? string? str) (StringC str)]
    [(? symbol? sym)
     (cond
       [(hash-has-key? invalidArguments sym) (error 'parse "RGME: These Symbols not Legal Arguments")]
       [else (IdC sym)])]
    [(list 'if c t e) (IfC (parse c) (parse t) (parse e))]
    [(list 'var (list var '= expression) ...) (error 'parse: "RGME: Var with no body")]
    [(list 'var (list var '= expression)... id) (desugar expr)]
    [(list (? symbol? id) '<- setExpr) (SetC id (parse setExpr))]
    [(list 'begin exp1 ...) (SeqC (map parse exp1))]
    [(list 'lam (list id ...) e)
     (define list-Symbols?
       (lambda (x) (cond
                     [(symbol? x) x]
                     [else (error "RGME: Argument not a Symbol")])))
     (define newLambda (LamC (map list-Symbols? (second expr)) (parse e)))
     (cond
       [(not(or (check-duplicates (LamC-param newLambda))
                (invalcheckSymbols (LamC-param newLambda)))) newLambda]
       [else (error "RGME: Lambda Invalid Arguments")])]
    [(list expr1 expr2 ...)
     (cond
       [(hash-has-key? invalidArguments expr1) (error 'parse "RGME: These Symbols not Legal Arguments")]
       [else
        (let*
            ([function (parse expr1)])
          (match function
            [(LamC lamArg lamBody)
             (cond
               [(not (eq? (length lamArg) (length (rest expr))))
                (error 'parse "RGME: Number of Arguments do not Equal")]
               [else (AppC function (map parse expr2))])]
            [else (AppC function (map parse expr2))]))])]
    [else (error 'parse "RGME: Invalid Input")]))

;test cases for parse
(check-equal? (parse 42)(NumC 42))
(check-equal? (parse 'simo)(IdC 'simo))
(check-equal? (parse "SIMO")(StringC "SIMO"))
(check-equal? (parse '{SIMO})(AppC (IdC 'SIMO)'()))
(check-equal? (parse '{"SIMO"})(AppC (StringC "SIMO")'()))
(check-equal? (parse '{if false {+ 1 1}{- 1 1}})
              (IfC (IdC 'false) (AppC (IdC '+) (list (NumC 1) (NumC 1))) (AppC (IdC '-) (list (NumC 1) (NumC 1)))))
(check-equal? (parse '{lam {a b}{* a b}})
              (LamC '(a b) (AppC (IdC '*) (list (IdC 'a) (IdC 'b)))))
(check-equal?  (parse '{var {z = {+ 9 14}}{y = 98}{+ z y}})
               (AppC (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                     (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-equal? (parse '{lam {a b}{* a b}})
              (LamC '(a b) (AppC (IdC '*) (list (IdC 'a) (IdC 'b)))))
(check-exn (regexp (regexp-quote "RGME: Invalid Input"))
           (lambda ()(parse #f)))
(check-exn (regexp (regexp-quote "RGME: These Symbols not Legal Arguments"))
           (lambda ()(parse '{+ if lam})))
(check-exn (regexp (regexp-quote "RGME: Var with duplicate Args"))
           (lambda ()(parse '{var {x = 1}{x = 2}{+ x 10}})))
(check-exn (regexp (regexp-quote "RGME: Var with no body"))
           (lambda ()(parse '{var {x = 1}{y = 2}})))
(check-exn (regexp (regexp-quote "RGME: These Symbols not Legal Arguments"))
           (lambda ()(parse '{100 = z})))
(check-exn (regexp (regexp-quote "RGME: Number of Arguments do not Equal"))
           (lambda ()(parse '{{lam {a b}{* 5 b}} 40})))
(check-exn (regexp (regexp-quote "RGME: Argument not a Symbol"))
           (lambda ()(parse '{lam {10 b}{* 5 b}})))
(check-exn (regexp (regexp-quote "RGME: Lambda Invalid Arguments"))
           (lambda ()(parse '{lam {if}{* 5 b}})))
(check-exn (regexp (regexp-quote "RGME: These Symbols not Legal Arguments"))
           (lambda ()(parse '{lam 5 b})))
(check-equal? (V*S-val (interp (parse '{substring "Mohamed" 0 3}) top-env top-sto)) (StringV "Moh"))
(check-exn (regexp (regexp-quote "RGME: Non Conditional Statement Passed"))
           (lambda () (interp (IfC (AppC (LamC (list 'x 'y) (AppC (IdC '-) (list (IdC 'x) (IdC 'y))))
                                         (list (NumC 4) (NumC 5)))
                                   (NumC 5) (NumC -5)) top-env top-sto)))
(check-equal? (V*S-val(interp (parse '{var {fact = "Maroc"}
                                           {fact <- 44}}) top-env top-sto)) (NullV null))
(check-equal? (V*S-val (interp (parse '{begin {+ 4 9} {- 2 4}}) top-env top-sto)) (NumV -2))
(check-equal? (V*S-val (interp (parse '{array 4 true 8}) top-env top-sto))
              (ArrayV 3 (make-immutable-hash(list (cons 1 (NumV 4))
                                                  (cons 2 (BoolV #t))
                                                  (cons 3 (NumV 8))))))
(check-exn (regexp (regexp-quote  "RGME: Illegal Id"))
           (lambda () (desugar '(var (x = 2) (lam = 4) (+ x lam)))))
(check-equal? (parse '{if true {+ 2 5} {- 5 2}})
              (IfC (IdC 'true) (AppC (IdC '+) (list (NumC 2) (NumC 5))) (AppC (IdC '-) (list (NumC 5) (NumC 2)))))
(check-equal? (parse '{lam {x y} {/ x y}}) (LamC '(x y) (AppC (IdC '/) (list (IdC 'x) (IdC 'y)))))
(check-equal? (parse '{var {x = 98} {y = {+ 14 9}} {+ x y}})
              (AppC (LamC '(x y)
                          (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                    (list (NumC 98) (AppC (IdC '+) (list (NumC 14) (NumC 9))))))
(check-exn (regexp (regexp-quote "RGME: Var with duplicate Args"))
           (lambda () (parse '((var (x = 99) (x = 99) (* 2 x))))))
(check-exn (regexp (regexp-quote  "RGME: Var with no body"))
           (lambda () (parse '(var (x = 99) (y = 99)))))
(check-exn (regexp (regexp-quote "RGME: These Symbols not Legal Arguments"))
           (lambda () (parse '{98 = a})))
(check-exn (regexp (regexp-quote "RGME: These Symbols not Legal Arguments"))
           (lambda () (parse '{if a b})))
(check-exn (regexp (regexp-quote "RGME: Argument not a Symbol"))
           (lambda () (parse '{lam {3 y} {+ 3 y}})))
(check-exn (regexp (regexp-quote  "RGME: Illegal Id"))
           (lambda () (parse '(var (lam = "") "World"))))

;top-interp takes in a Sexp and parses then interprets the entire expression
;to a Value type. This Value is then serialized and the function returns a String.
(define (top-interp [s : Sexp]) : String
  (serialize (V*S-val (interp (parse s) top-env top-sto))))

;test cases for top-inerp
(check-equal? (top-interp '{* 4 5}) "20")
(check-equal? (top-interp '{/ 15 5}) "3")
(check-equal? (top-interp '{+ 15 5}) "20")
(check-equal? (top-interp '{- 15 5}) "10")
(check-equal? (top-interp '{<= 15 5}) "false")
(check-equal? (top-interp '{<= 2 5}) "true")
(check-equal? (top-interp '{equal? true false}) "false")
(check-equal? (top-interp '{equal? false false}) "true")
(check-equal? (top-interp '{equal? "SIMO" "SIMO"}) "true")
(check-equal? (top-interp '{if {<= 10 5}{* 10 2}(/ 10 2)}) "5")
(check-exn (regexp (regexp-quote "RGME: AppC - Bad Syntax"))
           (lambda ()(top-interp '{{{lam {} 5}} 6 7})))




