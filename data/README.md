## Data for benchmarking 

This directory contains common data that are used for benchmarking across different ecosystems 
(OCaml and Haskell -- and optionally Racket).

### Commands 

- `racket generate-random-trees.rkt --out out-file.sexp --fit 1000` would generate a file 
   in the same format as `random-tree-1.sexp` at `out-file.sexp`, containing a tree from 
   a Dyck path of length 1000. `--fit` ensures that the generated tree can be pretty printed 
   to fit the page width limit (default to 80). See `--help` for details.
   This is done by consulting `sexp-random` benchmarking program in Haskell to make sure that 
   the tree can fit the page width limit.
