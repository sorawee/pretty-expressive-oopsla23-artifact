#lang racket

(provide run-task string->nat benchmark-result-dir)

(require "common.rkt")

(current-subprocess-custodian-mode 'kill)

(define (run-task #:program program
                  #:name [name #f]
                  #:out [out #f]
                  #:extras [extras '()])

  (define (run-it outp)
    (define (print-value p)
      (when outp
        (pretty-display p outp))
      (pretty-display p))

    (define port/stdout (open-output-string))
    (define port/stderr (open-output-string))
    (putenv "PLTSTDERR" "debug@fmt")
    (match-define (list _ _ _ _ proc)
      (apply process*/ports
             port/stdout
             (current-input-port)
             port/stderr
             (append (list (find-executable-path "raco") "fmt")
                     extras
                     (list (build-path "fmt/tests/benchmarks" program)))))
    (proc 'wait)
    (when out
      (with-output-to-file out
        #:exists 'replace
        (λ () (displayln (get-output-string port/stdout)))))
    (print-value (list* `(name ,name)
                        (read (open-input-string (get-output-string port/stderr))))))

  (parameterize ([subprocess-group-enabled #t])
    (cond
      [name
       (call-with-output-file* (build-path benchmark-result-dir name)
         #:exists 'append
         run-it)]
      [else (run-it #f)])))

(define (string->nat #:who who n)
  (match (string->number n)
    [(? natural? nn) nn]
    [_ (raise-user-error (format "~a must be a natural number, got ~a" who n))]))

(module+ main
  (require racket/cmdline)

  (define name #f)
  (define program #f)
  (define iter 1)
  (define extras '())
  (define out #f)

  (command-line
   #:once-each
   [("--name")
    the-name
    "Filename for logging (optional, default: no logging)"
    (set! name the-name)]
   [("--program")
    the-program
    "Benchmark program"
    (set! program the-program)]
   [("--page-width")
    the-page-width
    "Page width limit (optional)"
    (set! extras (append (list "--width" the-page-width) extras))]
   [("--computation-width")
    the-computation-width
    "Computation width limit (optional, only for pretty-expressive printers)"
    (set! extras (append (list "--limit" the-computation-width) extras))]
   [("--iter")
    the-iter
    "Iterations (optional, default: 1)"
    (set! iter (string->nat #:who "--iter" the-iter))]
   [("--out")
    the-out
    ["Output the actual layout to a specified path;"
     "(default: do not output)"]

    (when (equal? "-" the-out)
      (raise-user-error "invalid path (outputting to stdout is not supported)"))

    (set! out the-out)])

  (unless program
    (raise-user-error "--program must be specified"))

  (for ([i iter])
    (run-task #:name name #:program program #:out out #:extras extras)))
