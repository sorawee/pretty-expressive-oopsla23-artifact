#lang racket

(define TMPPATH "random-tree-0.sexp")
(require json)

(define (dyck len)
  (let loop ([opened 0] [closed 0])
    (cond
      [(>= closed len) '()]
      [(or (>= opened len)
           (and (< closed opened)
                (zero? (random 2))))
       (cons 'close (loop opened (add1 closed)))]
      [else
       (cons 'open (loop (add1 opened) closed))])))

(define (parse xs)
  (match xs
    [(list 'open xs ...)
     (match-define (cons content rest) (parse-content xs))
     (cons content rest)]
    [(list x xs ...)
     (cons x xs)]))

(define (parse-content xs)
  (match xs
    ['() (error 'impossible)]
    [(list 'close xs ...) (cons '() xs)]
    [_
     (match-define (cons one rest) (parse xs))
     (match-define (cons results rest*) (parse-content rest))
     (cons (cons one results) rest*)]))

(define (parse-number s who)
  (define n (string->number s))
  (cond
    [(exact-nonnegative-integer? n) n]
    [else (raise-user-error
           (format "expect ~a to be a natural number" who))]))

(define (fitting? width)
  (define cabal (find-executable-path "cabal"))
  (parameterize ([current-directory "../other-artifacts"])
    (system* cabal
             "run"
             "sexp-random"
             "--"
             "--target" "bernardy-paper"
             "--size" "0"
             "--page-width" (~a width))))

(module+ main
  (define current-width 80)
  (define current-fit #f)
  (define current-out #f)
  (define current-size #f)

  (command-line
   #:once-each
   [("--width") width "Width limit for --fit"
                (set! current-width (parse-number width "width"))]
   [("--fit") "Generate a fitting S-exp"
              (set! current-fit #t)]
   [("--out") out "Output path"
              (set! current-out out)]
   #:args (size)
   (set! current-size (parse-number size "size")))

  (define (print-it)
    (define path (append (list 'open)
                         (add-between (dyck current-size) "A")
                         (list 'close)))
    (match-define (cons parsed _) (parse path))
    (with-output-to-file TMPPATH #:exists 'replace
      (λ () (write-json parsed))))

  (print-it)

  (when current-fit
    (let loop ()
      (unless (fitting? current-width)
        (printf "Failed to generate a fitting tree; try again\n")
        (print-it)
        (loop))))

  (cond
    [current-out (rename-file-or-directory TMPPATH current-out)]
    [else (displayln (file->string TMPPATH))]))
