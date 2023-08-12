#lang racket

(provide all-ids)
(require "gen-table-2-cell.rkt"
         "common.rkt")

(define all-ids
  '([concat10k concat 10000]
    [concat50k concat 50000]
    [fillsep5k fill-sep 5000]
    [fillsep50k fill-sep 50000]
    [flatten8k flatten 8000]
    [flatten16k flatten 16000]
    [sexpfull15 sexp-full 15]
    [sexpfull16 sexp-full 16]
    [randfit1k sexp-random 1]
    [randfit10k sexp-random 2]
    [randover1k sexp-random 3]
    [randover10k sexp-random 4]
    [json1k json 1]
    [json10k json 2]
    [jsonw json 1 #:page-width 50 #:computation-width 60]))

(module+ main
  (require racket/cmdline)

  (define iter 5)
  (define timeout 60)

  (define printers '())

  (define pretty-expressive-default "pretty-expressive-default")
  (define pretty-expressive-1000 "pretty-expressive-1000")
  (define leijen "leijen")
  (define bernardy-paper "bernardy-paper")
  (define bernardy-patched "bernardy-patched")

  (define valid-printers (list pretty-expressive-default
                               pretty-expressive-1000
                               leijen
                               bernardy-paper
                               bernardy-patched))

  (define ids
    (command-line
     #:multi
     [("--printer")
      p
      [(apply format "Printer to run (one of: [~a, ~a, ~a, ~a, ~a]," valid-printers)
       "default: run everything)"]
      (unless (member p valid-printers)
        (raise-user-error "invalid printer" p))
      (set! printers (cons p printers))]
     #:once-each
     [("--timeout")
      the-timeout
      "Timeout in seconds (optional, default: 60)"
      (set! timeout (string->nat #:who "--timeout" the-timeout))]
     [("--iter")
      the-iter
      "Iterations (optional, default: 10)"
      (set! iter (string->nat #:who "--iter" the-iter))]
     #:args ids
     (match ids
       ['() (map first all-ids)]
       [_
        (for/list ([id ids])
          (define sym-id (string->symbol id))
          (match (assoc sym-id all-ids)
            [#f (raise-user-error "the benchmark id is not recognized" sym-id)]
            [_ sym-id]))])))

  (for ([id ids])
    (printf "processing ~a\n" id)
    (match-define (list _ program size extras ...) (assoc id all-ids))

    (define (do-run target com-suffix com-proc)
      (run-task #:name (format "~a@~a@~a.dat" id target com-suffix)
                #:program (symbol->string program)
                #:target target
                #:timeout timeout
                #:extras (match extras
                           ['() (append (list "--size" (~a size) "--page-width" "80") (com-proc "100"))]
                           [(list '#:page-width page-width '#:computation-width computation-width)
                            (append (list "--size" (~a size) "--page-width" (~a page-width))
                                    (com-proc (~a computation-width)))])))

    (define (run-it name program variant computation-width-proc)
      (when (or (empty? printers) (member name printers))
        (for ([i iter])
          (do-run program variant computation-width-proc))))

    (run-it pretty-expressive-default
            "pretty-expressive-ocaml"
            "default"
            (λ (computation-width) (list "--computation-width" computation-width)))

    (run-it pretty-expressive-1000
            "pretty-expressive-ocaml"
            "1000"
            (λ (_) (list "--computation-width" "1000")))

    (run-it leijen
            "leijen"
            "none"
            (λ (_) '()))

    (run-it bernardy-paper
            "bernardy-paper"
            "none"
            (λ (_) '()))

    (run-it bernardy-patched
            "bernardy-patched"
            "none"
            (λ (_) '()))))
