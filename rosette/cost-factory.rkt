#lang rosette

(require syntax/parse/define)

(define-syntax-parse-rule (report name:string e binding ...)
  (let ()
    (newline)
    (define result e)
    (cond
      [(unsat? result)
       (printf "~a: verified\n" name)]
      [else
       (printf "~a:\n" name)
       (printf "~a = ~a\n" 'binding (evaluate binding result)) ...])))

(define (check name
               #:<= cost<=
               #:+ cost+
               #:text cost-text
               #:nl cost-nl
               #:get-cost* get-cost*)

  (clear-vc!)
  (clear-terms!)

  (printf "\n\n== ~a ==\n" name)

  (define c1 (get-cost*))
  (define c2 (get-cost*))
  (define c3 (get-cost*))
  (define c4 (get-cost*))

  ;; total ordering

  (report
   "transitivity"
   (verify (begin
             (assume (cost<= c1 c2))
             (assume (cost<= c2 c3))
             (assert (cost<= c1 c3))))
   c1 c2 c3)


  (report
   "antisym"
   (verify (begin
             (assume (cost<= c1 c2))
             (assume (cost<= c2 c1))
             (assert (equal? c1 c2))))
   c1 c2)

  (report
   "total"
   (verify (assert (|| (cost<= c1 c2) (cost<= c2 c1))))
   c1 c2)

  ;; +

  (report
   "+"
   (verify (begin
             (assume (cost<= c1 c2))
             (assume (cost<= c3 c4))
             (assert (cost<= (cost+ c1 c3) (cost+ c2 c4)))))
   c1 c2 c3 c4)

  ;; text and newline

  (define-symbolic col1 col2 len i1 i2 integer?)
  (assert (>= col1 0))
  (assert (>= col2 0))
  (assert (>= len 0))
  (assert (>= i1 0))
  (assert (>= i2 0))

  (report
   "text"
   (verify (begin
             (assume (<= col1 col2))
             (assert (cost<= (cost-text col1 len) (cost-text col2 len)))))
   col1 col2 len)

  (report
   "nl"
   (verify (begin
             (assume (<= i1 i2))
             (assert (cost<= (cost-nl i1) (cost-nl i2)))))
   i1 i2))

(define width 80)

(check "Ex 5.1"
       #:<= (match-lambda**
             [((list o1 h1) (list o2 h2))
              (cond
                [(= o1 o2) (<= h1 h2)]
                [else (< o1 o2)])])
       #:+ (match-lambda**
            [((list o1 h1) (list o2 h2))
             (list (+ o1 o2) (+ h1 h2))])
       #:text (λ (c l)
                (list (max (+ c l (- (max width c))) 0)
                      0))
       #:nl (λ (i) (list (max (- i width) 0) 1))
       #:get-cost* (λ ()
                     (define-symbolic* o h integer?)
                     (list o h)))

(check "max"
       #:<= (match-lambda**
             [(m1 m2) (<= m1 m2)])
       #:+ (match-lambda**
            [(m1 m2) (max m1 m2)])
       #:text (λ (c l) (max width (+ c l)))
       #:nl (λ (i) (max width i))
       #:get-cost* (λ ()
                     (define-symbolic* m integer?)
                     (assert (>= m 0))
                     m))

(check "max in lex ordering is bad"
       #:<= (match-lambda**
             [((list m1 o1 h1) (list m2 o2 h2))
              (cond
                [(= m1 m2)
                 (cond
                   [(= o1 o2) (<= h1 h2)]
                   [else (< o1 o2)])]
                [else (< m1 m2)])])
       #:+ (match-lambda**
            [((list m1 o1 h1) (list m2 o2 h2))
             (list (max m1 m2) (+ o1 o2) (+ h1 h2))])
       #:text (λ (c l)
                (list (max width (+ c l))
                      (max (+ c l (- (max width c))) 0)
                      0))
       #:nl (λ (i) (list (max width i) (max (- i width) 0) 1))
       #:get-cost* (λ ()
                     (define-symbolic* m o h integer?)
                     (assert (>= m 0))
                     (assert (>= o 0))
                     (assert (>= h 0))
                     (list m o h)))

(check "actual"
       #:<= (match-lambda**
             [((list o1 h1) (list o2 h2))
              (cond
                [(= o1 o2) (<= h1 h2)]
                [else (< o1 o2)])])
       #:+ (match-lambda**
            [((list o1 h1) (list o2 h2))
             (list (+ o1 o2) (+ h1 h2))])
       #:text (λ (c l)
                (define stop (+ c l))
                (cond
                  [(> stop width)
                   (define start (max width c))
                   (define a (- start width))
                   (define b (- stop start))
                   (list (* b (+ (* 2 a) b)) 0)]
                  [else (list 0 0)]))
       #:nl (λ (i) (list 0 1))
       #:get-cost* (λ ()
                     (define-symbolic* o h integer?)
                     (assert (>= o 0))
                     (assert (>= h 0))
                     (list o h)))
