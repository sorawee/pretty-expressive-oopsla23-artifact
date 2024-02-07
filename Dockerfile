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
# merge
COPY lean /workspace/lean
RUN racket scripts/gen-main.rkt

###################################################
# Clone implementations

WORKDIR /workspace
RUN git clone https://github.com/sorawee/pretty-expressive-ocaml
RUN git clone https://github.com/sorawee/pretty-expressive pretty-expressive-racket
RUN git clone https://github.com/sorawee/fmt.git

# merge
COPY pretty-expressive-ocaml /workspace/pretty-expressive-ocaml

WORKDIR /workspace/pretty-expressive-ocaml
RUN opam install -y --working-dir . --with-test
RUN eval $(opam config env) && dune build --release

WORKDIR /workspace/pretty-expressive-racket
RUN raco pkg install --auto --name pretty-expressive

WORKDIR /workspace/fmt
RUN raco pkg install --auto

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
