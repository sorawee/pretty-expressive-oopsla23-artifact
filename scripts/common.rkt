#lang racket

(provide benchmark-result-dir string->nat)

(define benchmark-result-dir (simple-form-path "benchmark-results"))

(define (string->nat #:who who n)
  (match (string->number n)
    [(? natural? nn) nn]
    [_ (raise-user-error (format "~a must be a natural number, got ~a" who n))]))
