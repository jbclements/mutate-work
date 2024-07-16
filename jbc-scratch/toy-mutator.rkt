#lang at-exp racket

;; just messing around with mutation

(require mutate
         syntax/parse
         racket/stream)
 
(define program-mutations
  (build-mutation-engine
   #:mutators
   (define-simple-mutator (permute-cond stx)
     #:pattern ({~datum cond} [tests argses ...] ...)
     (bogus-id
      (for/stream ([args (in-list (attribute argses))])
        #`(begin #,@args))))
   #:syntax-only
   #:streaming
   #:module-mutator))

(define (bogus-id x) x)

(define program-to-mutate
  #'(module test-program racket
      (#%module-begin
       (require "a.rkt")
       (cond [(try1) 'answer1]
             [(try2) 'answer2 'answer2andahalf]
             [(try3) 'answer3])
       (displayln y))))

(map syntax->datum (stream->list (program-mutations program-to-mutate)))

