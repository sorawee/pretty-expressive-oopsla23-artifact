#lang racket

(define filename "import_graph.dot")

(match-define (list pre content ... post) (file->lines filename))

(define content*
  (for/list ([entry content]
             #:do [(define p (open-input-string entry))
                   (define from (read p))
                   (read p)
                   (define to (read p))]
             #:when (string-prefix? from "Pretty.")
             #:when (string-prefix? to "Pretty."))
    (format "~s -> ~s;" from to)))

(with-output-to-file filename
  #:exists 'replace
  (λ ()
    (displayln pre)
    (for ([entry content*])
      (displayln entry))
    (displayln post)))
