FROM soraweep/pretty-expressive-oopsla23-artifact:base

###################################################
# Copy Haskell printers, benchmarks, and build them

COPY other-artifacts/ /workspace/other-artifacts
WORKDIR /workspace/other-artifacts

RUN cp -r ../prettiest/Text Text
COPY bernardy-remove-width-limit.patch .
RUN patch -p1 < bernardy-remove-width-limit.patch
RUN mv Text TextPatched

RUN cp -r ../prettiest/Text Text

RUN cabal build

###################################################

WORKDIR /workspace/lean
COPY lean/Pretty Pretty
COPY lean/Makefile Makefile
COPY lean/scripts scripts
COPY lean/README.md README.md
COPY lean/.gitignore .gitignore
COPY lean/Pretty.lean Pretty.lean

###################################################
# Clone implementations (fmt and pretty-expressive-racket)

WORKDIR /workspace
RUN git clone https://github.com/sorawee/pretty-expressive pretty-expressive-racket
RUN git clone https://github.com/sorawee/fmt.git

WORKDIR /workspace/pretty-expressive-racket
RUN raco pkg install --auto --name pretty-expressive

WORKDIR /workspace/fmt
RUN raco pkg install --auto

###################################################
# Copy OCaml printer, benchmarks, and build them

COPY pretty-expressive-ocaml /workspace/pretty-expressive-ocaml
WORKDIR /workspace/pretty-expressive-ocaml
RUN eval $(opam config env) && dune build

###################################################

# Get Z3 working
COPY rosette /workspace/rosette
WORKDIR /workspace/rosette
RUN racket setup-z3.rkt

###################################################
# Copy data

COPY data /workspace/data
ENV BENCHDATA /workspace/data
RUN echo 'export BENCHDATA=/workspace/data' >> ~/.bashrc

COPY scripts /workspace/scripts
COPY benchmark-results /workspace/benchmark-results
COPY output-dir /workspace/output-dir

WORKDIR /workspace

COPY README.md README.md

###################################################
# Done
