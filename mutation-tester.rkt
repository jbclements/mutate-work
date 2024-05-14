#lang at-exp racket

(require syntax/parse
         mutate
         mutate/traversal
         mutate/logger
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

;; create a listener that is interested in all
;; messages on the fooabc logger with topic 'debug or higher
(define log-receiver
  (make-log-receiver mutate-logger 'debug))

(define score
  (for/fold ([failure 0]
             [total 0]
             #:result (/ failure total))
            ([mutant-stx (get-mutants "430Asgn/Asgn3.rkt")])
    (define temp (make-temporary-file  "mutant-~a"))
    (write-to-file (syntax->datum mutant-stx)
                   temp
                   #:exists 'replace)
    (define message
       (sync log-receiver))
     ;; print out the message:
     (printf "\n\nMutator used: ~e\n" message)
    (define tests-pass?
      (system* (find-executable-path "raco")
               "test"
               temp))
    (delete-file temp)
    (values (+ failure (if tests-pass? 0 1))
            (add1 total))))


(displayln (~a "\n\nMutation score: " (~r score)))

#;(thread
 (λ ()
   ;; run infinitely:
   (let loop ()
     ;; block until a message is received:
     (define message
       (sync log-receiver))
     ;; print out the message:
     (printf "\n\nMutator used: ~e" message)
     ;; continue waiting:
     (loop))));#