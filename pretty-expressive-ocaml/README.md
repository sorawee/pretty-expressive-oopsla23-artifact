## OCaml SnowWhite

Please consults the artifact overview for details.

### Contents 

- `pretty`: source code of the pretty printer
- `examples`: example programs that use the pretty printer
- `benchmarks`: benchmarks from paper (and some more benchmark programs)
- `benchtool`: benchmarking framework

### Commands

- `./run.sh </path/to/file.ml>`: run a program. For example:
  - `./run.sh examples/fig_1.ml`: run an example program `fig_1.ml`
  - `./run.sh benchmarks/concat.ml`: run a benchmark program `concat.ml`
  - `./run.sh benchmarks/concat.ml -- -help`: view options to run a benchmark
- `make build`: build all executables
- `make doc`: generate HTML doc (not necessarily runnable in Docker)
- `make run-server`: spawn a server for viewing HTML doc (not necessarily runnable in Docker)
