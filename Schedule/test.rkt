#lang racket

;; create a logger called fooabc:
(define-logger fooabc)

;; create a listener that is interested in all
;; messages on the fooabc logger with topic 'debug or higher
(define log-receiver
  (make-log-receiver fooabc-logger 'debug))


;; start a thread to print out messages that are recieved
(thread
 (λ ()
   ;; run infinitely:
   (let loop ()
     ;; block until a message is received:
     (define message
       (sync log-receiver))
     ;; print out the message:
     (printf "got a message! It said: ~e\n" message)
     ;; continue waiting:
     (loop))))

;; let's send some log messages:
(log-fooabc-debug "hello1")
(log-fooabc-debug "hello2")