#lang racket

(define (schedule dates things constraints)
  (define number-of-days (length dates))
  (define schedule
    (list->vector
     (flatten
      (list
       (build-list (floor (/ number-of-days (length things)))
                   (λ _ (shuffle things)))
       (take (shuffle things)
             (modulo number-of-days (length things)))))))

  (define (conflicts? index date)
    (define team (vector-ref schedule index))
    (member date (hash-ref constraints team empty)))
  (define (fixup-position! i i-date)
    (define fixed?
      (for/or ([o-date (in-list date)]
               [o      (in-range number-of-days)]
               #:when (and (not (conflicts? i o-date))
                           (not (conflicts? o i-date))))
        (define i-team (vector-ref schedule i))
        (define o-team (vector-ref schedule o))
        (vector-set! schedule i o-team)
        (vector-set! schedule o i-team)
        #t))
    (unless fixed?
      (error 'schedule "Couldn't find a feasible date for ~a" (vector-ref schedule i))))

  (for ([date (in-list dates)]
        [i    (in-range number-of-days)])
        (when (conflicts? i date)
          (fixup-position! i date)))
  
  (map list
       dates
       (vector->list schedule)))

(random-seed 12342243)
(module+ test
  (require rackunit)
  (check-equal? (schedule '() '(A) (hash))
                '())
  (check-equal? (schedule '(1) '(A) (hash))
                '((1 A)))
  (check-true (and (member (schedule '(1 2) '(A B) (hash))
                            '[((1 A) (2 B))
                              ((1 B) (2 A))])
                    #t))
  (check-equal? (schedule '(1 2) '(A B) (hash 'A '(1)))
                '((1 B) (2 A))))
                    