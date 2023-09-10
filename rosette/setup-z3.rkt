#lang racket

(require file/unzip)

;; adapted from rosette/private/install.rkt
(define (pre-install racl-path)
  (define bin-path (simplify-path (build-path racl-path ".." "bin")))
  (define z3-path (build-path bin-path "z3"))
  (make-directory* bin-path) ;; Ensure that `bin-path` exists
  (delete-directory/files z3-path #:must-exist? #f) ;; Delete old version of Z3, if any
  (define z3-path-in-zip "z3-4.12.3-arm64-glibc-2.35/bin/z3")
  (call-with-input-file* "z3-4.12.3-arm64-glibc-2.35.zip"
    (λ (z3-port)
      (parameterize ([current-directory bin-path])
        (call-with-unzip z3-port
                         (λ (dir)
                           (copy-directory/files (build-path dir z3-path-in-zip) z3-path)))
        ;; Unzipping loses file permissions, so we reset the z3 binary here
        (file-or-directory-permissions
         z3-path
         (if (equal? (system-type) 'windows) #o777 #o755))))))

(match* ((system-type 'os*) (system-type 'arch))
  [('linux 'aarch64)
   (pre-install (path-only (collection-file-path "main.rkt" "rosette")))]
  [(_ _) (void)])
