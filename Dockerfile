FROM ubuntu:22.04

###################################################
# General installation

WORKDIR /workspace

RUN apt-get update && apt-get install -y \
    git \
    htop \
    vim \
    # Dependencies for https://www.haskell.org/ghcup/install/
    build-essential \
    curl \
    libffi-dev \
    libffi7 \
    libgmp-dev \
    libgmp10 \
    libncurses-dev \
    libncurses5 \
    libtinfo5 \
    llvm \
    libnuma-dev \
    # Racket and OCaml
    racket \
    opam \
    # Workaround to make raco pkg install work
    # See https://github.com/racket/racket/issues/4306
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

###################################################
# GHC installation

ENV BOOTSTRAP_HASKELL_NONINTERACTIVE=1

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

ENV PATH=${PATH}:/root/.local/bin:/root/.ghcup/bin

###################################################

RUN git clone https://github.com/jyp/prettiest

WORKDIR /workspace/prettiest

# The camera-ready version of Bernardy's paper
ARG BERNARDY_PRINTER_COMMIT=5e7a12cf37bb01467485bbe1e9d8f272fa4f8cd5

RUN git checkout $BERNARDY_PRINTER_COMMIT

###################################################
# Setup OCaml and Racket

RUN opam init -y
RUN opam install -y odoc ppx_import yojson core_unix core dune stdio
RUN echo 'eval $(opam config env)' >> ~/.bashrc

# Workaround for the "docs failure: query-exec: unable to open the database file" issue
# See https://github.com/racket/racket/issues/2691
RUN raco setup --doc-index --force-user-docs

RUN raco pkg install --auto text-table

###################################################
# Install elan + lean

RUN curl -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
RUN chmod +x elan-init.sh
RUN ./elan-init.sh -y --default-toolchain "leanprover/lean4:nightly-2023-02-23"
RUN rm elan-init.sh
ENV PATH=${PATH}:/root/.elan/bin

WORKDIR /workspace
COPY lean/ lean
WORKDIR /workspace/lean
RUN lake update
RUN lake build
RUN lake clean

###################################################

WORKDIR /workspace

RUN cabal install --lib \
    base-compat-0.12.2 \
    optparse-applicative-0.17.0.0 \
    aeson-2.1.2.1 \
    attoparsec-0.14.4 \
    wl-pprint-1.2.1

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
# Copy data

COPY data /workspace/data
ENV BENCHDATA /workspace/data
RUN echo 'export BENCHDATA=/workspace/data' >> ~/.bashrc

COPY scripts /workspace/scripts
COPY benchmark-results /workspace/benchmark-results
COPY pdf /workspace/pdf
COPY output-dir /workspace/output-dir

WORKDIR /workspace

COPY artifact-overview.md artifact-overview.md

###################################################
# Done
