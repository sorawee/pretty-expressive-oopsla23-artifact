#lang racket

(provide all-ids)

(require "gen-table-3-cell.rkt")

(define all-ids
  '("class-internal.rkt"
    "xform.rkt"
    "list.rkt"
    "hash.rkt"))

(module+ main
  (require racket/cmdline)

  (define iter 5)

  (define ids
    (command-line
     #:once-each
     [("--iter")
      the-iter
      "Iterations (optional, default: 10)"
      (set! iter (string->nat #:who "--iter" the-iter))]
     #:args ids
     (match ids
       ['() all-ids]
       [_ ids])))

  (for ([id ids])
    (printf "processing ~a\n" id)

    (define (do-run page-width computation-width)
      (run-task #:name (format "~a@~a.dat" id computation-width)
                #:program id
                #:extras (list "--width" page-width
                               "--limit" computation-width)))

    (for ([i iter])
      (do-run "80" "100"))

    (for ([i iter])
      (do-run "80" "1000"))))
