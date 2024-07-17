#lang racket


(require racket/syntax
        syntax/parse)

(define (grab-random lst)
  (list-ref lst (random (length lst))))

;; Replaces a random element in the list with #f
(define (replace-random lst)
  (let ([index (random (length lst))])
    (append (take lst index) (list #f) (drop lst (+ index 1)))))

(define (replace-at-index lst index)
  (append (take lst index)
          (list #f)
          (drop lst (+ index 1))))

(define (generate-replacement-stream stx-list stx-ref)
  (let ([len (length stx-list)])
    (for/stream ([index (in-range len)])
      (datum->syntax
       stx-ref
       `(and ,@(replace-at-index (map syntax-e stx-list) index))))))


; (define (args-length stx)
;   (syntax-parse stx
;     [({~datum and} fst args ...)
;     ;  (with-syntax* ([(modified-args ...) (datum->syntax #'fst (replace-random (syntax->datum #'(fst args ...))))]
;         (with-syntax* ([(modified-args ...) (datum->syntax #'fst (syntax->datum #'(fst args ...)))]
;                         [leng (length (syntax->datum #'(modified-args ...)))]
;                         [(arg-stream ...)
;                          (for/stream ([i (in-range (syntax->datum #'leng))])
;                            #'(datum->syntax #'fst (replace-at-index (syntax->datum #'(fst args ...)) i)))])
;     ;    (for/stream ([i (in-range (syntax->datum #'leng))])
;     ;      #'(and (syntax->datum modified-args ...)))
;         #'(and arg-stream ...)
;          )]))

(define (get-variants stx)
  (syntax-parse stx
    [({~datum and} fst args ...)
        (generate-replacement-stream (syntax->list #'(fst args ...)) #'fst)]))

    ; (define-simple-mutator (aod-minus stx)
    ;     #:pattern ({~datum -} arg ...)
    ;     (for/stream ([args (in-list (attribute arg))])
    ;     #`(begin #,@args)))

; (define (simple-func stx)
;   (syntax-parse stx
;     [({~datum and} fst args ...)
;      (with-syntax ([(modified-args ...) (datum->syntax #'fst (replace-random (syntax->datum #'(fst args ...))))])
;        #'(and modified-args ...))
;      ]))


;; Example usage
; (simple-func #'(and 1 2 3 4))
(define my-stream (get-variants #'(and 1 2 3 4)))
(for ([i (in-range 4)])
  (displayln (syntax->datum (stream-ref my-stream i))))


; (define-syntax (hyphen-define/ok2 stx)
;     (syntax-case stx ()
;       [(_ a b (args ...) body0 body ...)
;        (with-syntax ([name (datum->syntax #'a
;                                           (string->symbol (format "~a-~a"
;                                                                   (syntax->datum #'a)
;                                                                   (syntax->datum #'b))))])
;          #'(define (name args ...)
;              body0 body ...))]))

