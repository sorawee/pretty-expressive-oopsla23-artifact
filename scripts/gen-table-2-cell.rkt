#lang racket

(provide run-task string->nat benchmark-result-dir)

(require "common.rkt")

(current-subprocess-custodian-mode 'kill)

(define (run-task #:program program
                  #:target target
                  #:timeout timeout
                  #:name [name #f]
                  #:extras [extras '()])
  (define-values (dir prefix)
    (match target
      ["pretty-expressive-ocaml"
       (values "pretty-expressive-ocaml"
               (list "run.sh"
                     (format "benchmarks/~a.ml" (string-replace program "-" "_")) "--"))]
      ["pretty-expressive-racket"
       (values "pretty-expressive-racket"
               (list (find-executable-path "racket")
                     (format "benchmarks/~a.rkt" program)))]
      [(or "bernardy-paper" "bernardy-patched" "leijen")
       (values "other-artifacts"
               (list (find-executable-path "cabal")
                     "run" "--verbose=0" program "--"
                     "--target" target))]
      [_ (raise-user-error "unrecognized target:" target)]))

  (define (run-it outp)
    (define (print-value p)
      (when outp
        (pretty-display p outp))
      (pretty-display p))

    (define port/stdout (open-output-string))
    (define port/stderr (open-output-string))
    (define cust (make-custodian))
    (parameterize ([current-custodian cust])
      (match-define (list _ _ _ _ proc)
        (apply process*/ports
               port/stdout
               (current-input-port)
               port/stderr
               (append prefix extras)))
      (define thd (thread (λ () (proc 'wait))))
      (match (sync/timeout timeout thd)
        [#f
         (proc 'kill)
         (print-value `([name ,name]
                        [status timeout]))]
        [_
         (cond
           [(zero? (proc 'exit-code))
            (print-value (list* `(name ,name)
                                '(status ok)
                                (read (open-input-string (get-output-string port/stdout)))))]
           [else
            (print-value `([name ,name]
                           [status failure]
                           [stderr ,(~s (get-output-string port/stderr))]))])]))

    (custodian-shutdown-all cust))

  (parameterize ([current-directory dir]
                 [subprocess-group-enabled #t])
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
  (define target #f)
  (define program #f)
  (define iter 1)
  (define timeout 60)
  (define extras '())

  (command-line
   #:once-each
   [("--name")
    the-name
    "Filename for logging (optional, default: no logging)"
    (set! name the-name)]
   [("--target")
    the-target
    ["Target, which is one of:"
     "- pretty-expressive-ocaml"
     "- pretty-expressive-racket"
     "- leijen"
     "- bernardy-paper"
     "- bernardy-patched"]
    (set! target the-target)]
   [("--program")
    the-program
    "Benchmark program"
    (set! program the-program)]
   [("--size")
    the-size
    "Input size or variant (optional)"
    (set! extras (append (list "--size" the-size) extras))]
   [("--page-width")
    the-page-width
    "Page width limit (optional)"
    (set! extras (append (list "--page-width" the-page-width) extras))]
   [("--computation-width")
    the-computation-width
    "Computation width limit (optional, only for pretty-expressive printers)"
    (set! extras (append (list "--computation-width" the-computation-width) extras))]
   [("--timeout")
    the-timeout
    "Timeout in seconds (optional, default: 60)"
    (set! timeout (string->nat #:who "--timeout" the-timeout))]
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

    (set! extras (append (list "--out" (simple-form-path the-out)) extras))])

  (unless (and program target)
    (raise-user-error "--program, and --target must be specified"))

  (for ([i iter])
    (run-task #:name name #:program program #:target target #:timeout timeout #:extras extras)))
