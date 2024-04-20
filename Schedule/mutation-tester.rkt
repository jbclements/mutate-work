#lang at-exp racket

(require syntax/parse
         mutate
         mutate/traversal
         "./read-module.rkt"
         )

(define stx->mutants
  (build-mutation-engine
   #:mutators
   (define-id-mutator swap-ids
     [/ #:-> modulo]
     [/ #:-> *]
     [not #:-> identity]
     [and #:<-> or]
     [when #:<-> unless]
     [> #:<-> >=]
     [< #:<-> <=]
     )
   (define-simple-mutator (div-swap stx)
     #:pattern ({~datum /} e1 e2)
     #' (/ e2 e1))
   (define-constant-mutator (constant-swap v)
     [(? number?) #:-> (- v)])
   #:syntax-only
   #:top-level-selector select-define-body
   #:streaming
   #:module-mutator))

(define (get-mutants p)
  (stx->mutants (read-module p)))

(define score
  (for/fold ([failure 0]
             [total 0]
             #:result (/ failure total))
            ([mutant-stx (get-mutants "triangle.rkt")])
    (define temp (make-temporary-file  "mutant-~a"))
    (write-to-file (syntax->datum mutant-stx)
                   temp
                   #:exists 'replace)
    (define tests-pass?
      (system* (find-executable-path "raco")
               "test"
               temp))
    (delete-file temp)
    (values (+ failure (if tests-pass? 0 1))
            (add1 total))))


  (displayln (~a "\n\nMutation score: " (~r score)))