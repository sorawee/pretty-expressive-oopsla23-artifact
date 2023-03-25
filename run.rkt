#lang racket

(current-subprocess-custodian-mode 'kill)

(define our-directory "prettiester")
(define their-directory "artifacts")

(define (task name sizes
              #:ours our-name
              #:theirs their-name
              #:their-printers printers
              #:extra [extra '()])
  (printf ">>> Running task ~a\n" name)
  (parameterize ([current-directory our-directory])
    (for ([size sizes])
      (printf "Running our printer with size ~a\n" size)
      (define thd
        (thread
         (λ ()
           (apply system* "run.sh" (format "./~a.ml" our-name)
                  "--"
                  "--iter" "1" "--size" (~a size) "--view-lines"
                  extra))))
      (match (sync/timeout 60 thd)
        [#f
         (kill-thread thd)
         (printf "info: timeout\n")]
        [_ (void)])))
  (parameterize ([current-directory their-directory])
    (for* ([printer printers] [size sizes])
      (printf "Running the printer ~a with size ~a\n" printer size)
      (define thd
        (thread
         (λ ()
           (apply system* (find-executable-path "cabal") "run" their-name
                  "--" "--target" printer
                  "--iter" "1" "--size" (~a size) "--view-lines"
                  extra))))
      (match (sync/timeout 60 thd)
        [#f
         (kill-thread thd)
         (printf "info: timeout\n")]
        [_ (void)]))))

#;
(task "FillSep"
      '(500 5000 50000)
      #:ours "test_fill_sep"
      #:theirs "test-fill-sep"
      #:their-printers '("wadler" "bernardy-paper" "bernardy-patched"))

#;
(task "SexpFull"
      '(14 15 16)
      #:ours "test_sexp_full"
      #:theirs "test-sexp-full"
      #:their-printers '("bernardy-paper" "bernardy-patched"))

#;
(task "JSON"
      '(1 2)
      #:ours "test_json"
      #:theirs "test-json"
      #:their-printers '("wadler" "bernardy-patched"))

#;
(task "SexpRandom"
      '(1 2 3 4)
      #:ours "test_sexp_random"
      #:theirs "test-sexp-random"
      #:their-printers '("bernardy-paper" "bernardy-patched"))

#;
(task "RepeatedFlatten"
      '(5000 10000)
      #:ours "test_repeated_flatten"
      #:theirs "test-repeated-flatten"
      #:their-printers '("wadler"))


#;
(task "Concat"
      '(10000 50000)
      #:ours "test_concat"
      #:theirs "test-concat"
      #:their-printers '("wadler" "bernardy-patched"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(task "JSONW"
      '(1 2)
      #:ours "test_json"
      #:theirs "test-json"
      #:their-printers '("wadler" "bernardy-patched")
      #:extra '("--width" "50"))
