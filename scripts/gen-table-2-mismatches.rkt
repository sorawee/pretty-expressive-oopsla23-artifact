#lang racket

(require "gen-table-2-cell.rkt")

(module+ main
  (displayln "Generating an output for RandFit1k on PrettyExpressive with 629 lines")
  (run-task #:program "sexp-random" #:target "pretty-expressive-ocaml" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randfit1k@629")
                           "--size" "1"))

  (displayln "Generating an output for RandFit1k on Leijen's printer with 943 lines")
  (run-task #:program "sexp-random" #:target "leijen" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randfit1k@943")
                           "--size" "1"))

  ;;;;;;;;;;

  (displayln "Generating an output for RandFit10k on PrettyExpressive with 7861 lines")
  (run-task #:program "sexp-random" #:target "pretty-expressive-ocaml" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randfit10k@7861")
                           "--size" "2"))

  (displayln "Generating an output for RandFit10k on Leijen's printer with 10459 lines")
  (run-task #:program "sexp-random" #:target "leijen" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randfit10k@10459")
                           "--size" "2"))

  ;;;;;;;;;;

  (displayln "Generating an output for RandOver1k on PrettyExpressive with 1531 lines")
  (run-task #:program "sexp-random" #:target "pretty-expressive-ocaml" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randover1k@1531")
                           "--size" "3"))

  (displayln "Generating an output for RandOver1k on Leijen's printer with 1635 lines")
  (run-task #:program "sexp-random" #:target "leijen" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randover1k@1635")
                           "--size" "3"))

  (displayln "Generating an output for RandOver1k on Bernardy's practical printer with 1105 lines")
  (run-task #:program "sexp-random" #:target "bernardy-patched" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randover1k@1105")
                           "--size" "3"))

  ;;;;;;;;;;

  (displayln "Generating an output for RandOver10k on PrettyExpressive with 15027 lines")
  (run-task #:program "sexp-random" #:target "pretty-expressive-ocaml" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randover10k@15027")
                           "--size" "4"))

  (displayln "Generating an output for RandOver10k on Leijen's printer with 16015 lines")
  (run-task #:program "sexp-random" #:target "leijen" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randover10k@16015")
                           "--size" "4"))

  (displayln "Generating an output for RandOver10k on Bernardy's practical printer with 7953 lines")
  (run-task #:program "sexp-random" #:target "bernardy-patched" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/randover10k@7953")
                           "--size" "4"))

  ;;;;;;;;;;

  (displayln "Generating an output for JSONW on PrettyExpressive with 721 lines")
  (run-task #:program "json" #:target "pretty-expressive-ocaml" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/jsonw@721")
                           "--size" "1"
                           "--page-width" "50"
                           "--computation-width" "60"))

  (displayln "Generating an output for JSONW on Bernardy's practical printer with 709 lines")
  (run-task #:program "json" #:target "bernardy-patched" #:timeout 60
            #:extras (list "--out" (simple-form-path "output-dir/jsonw@709")
                           "--size" "1"
                           "--page-width" "50")))
