#lang racket

(require text-table
         "common.rkt"
         (prefix-in table2: "gen-table-2.rkt")
         (prefix-in table3: "gen-table-3.rkt"))

(define all-targets '(["SnowWhite (default W)"
                       "pretty-expressive-ocaml"
                       "default"]
                      ["SnowWhite (W = 1000)"
                       "pretty-expressive-ocaml"
                       "1000"]
                      ["Wadler/Leijen"
                       "leijen"
                       "none"]
                      ["Bernardy (Naive)"
                       "bernardy-paper"
                       "none"]
                      ["Bernardy (Practical)"
                       "bernardy-patched"
                       "none"]))

(define (assc e lst)
  (second (assoc e lst)))

(displayln
 (table->string
  (cons (cons "Benchmark ID" (map first all-targets))
        (for/list ([id table2:all-ids])
          (cons (first id)
                (for/list ([target-entry all-targets])
                  (match-define (list _ target com-suffix) target-entry)
                  (define path (build-path benchmark-result-dir
                                           (format "~a@~a@~a.dat" (first id) target com-suffix)))
                  (cond
                    [(file-exists? path)
                     (define val (file->list path))
                     (match val
                       ['() "Unavailable"]
                       [_
                        (define-values (timeout failure ok ok-duration ok-lines ok-tainted?)
                          (for/fold ([timeout 0] [failure 0] [ok 0] [ok-duration 0] [ok-lines #f] [ok-tainted? #f]) ([entry val])
                            (match (assc 'status entry)
                              ['timeout (values (add1 timeout) failure ok ok-duration ok-lines ok-tainted?)]
                              ['failure (values timeout (add1 failure) ok ok-duration ok-lines ok-tainted?)]
                              ['ok
                               (values timeout failure (add1 ok)
                                       (+ ok-duration (assc 'duration entry))
                                       (assc 'lines entry)
                                       (if (equal? target "pretty-expressive-ocaml")
                                           (assc 'tainted? entry)
                                           #f))])))
                        (string-join
                         (append*
                          (list (if (positive? timeout) (list (format "~a timeout" timeout)) '())
                                (if (positive? failure) (list (format "~a N/A" failure)) '())
                                (if (positive? ok)
                                    (list
                                     (string-append
                                      (if (and (zero? timeout) (zero? failure))
                                          ""
                                          (format "~a OK: " ok))
                                      (format
                                       (if (equal? target "pretty-expressive-ocaml")
                                           (string-append "~a s | ~a | "
                                                          (match ok-tainted?
                                                            ['true "✗"]
                                                            ['false "✓"])
                                                          " ")
                                           "~a s | ~a ")
                                       (~r (/ ok-duration ok) #:min-width 10 #:precision '(= 6))
                                       (~a ok-lines #:min-width 6 #:align 'right))))
                                    '())))
                         ", ")])]
                    [else "Unavailable"])))))))

(newline)

(displayln
 (table->string
  (cons (list "Benchmark ID" "W = 100" "W = 1000")
        (for/list ([id table3:all-ids])
          (cons id
                (for/list ([com-limit '(100 1000)])
                  (define path (build-path benchmark-result-dir
                                           (format "~a@~a.dat" id com-limit)))
                  (cond
                    [(file-exists? path)
                     (define val (file->list path))
                     (match val
                       ['() "Unavailable"]
                       [(list fst _ ...)
                        (format "~a s | ~a | ~a "
                                (~r (/ (for/sum ([entry val])
                                         (assc 'duration entry))
                                       (length val))
                                    #:min-width 10
                                    #:precision '(= 6))
                                (~a (assc 'lines fst)
                                    #:min-width 6
                                    #:align 'right)
                                (match (assc 'tainted? fst)
                                  ['true "✗"]
                                  ['false "✓"]))])]
                    [else "Unavailable"])))))))

(newline)
(displayln
 (simple-table->string
  '(["Unavailable:" "not yet run to obtain data"]
    ["N/A:" "either failing to print or not applicable due to the lack of expressiveness"]
    ["Timeout:" "exceeding the time limit"])))
