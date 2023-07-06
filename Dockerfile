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
    libnuma-dev

###################################################
# GHC installation

ENV BOOTSTRAP_HASKELL_NONINTERACTIVE=1

# GHC installation could die due to memory limit of /tmp.
# so change TMPDIR
RUN mkdir /workspace/tmpdir
ENV TMPDIR="/workspace/tmpdir"

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

ENV PATH=${PATH}:/root/.local/bin
ENV PATH=${PATH}:/root/.ghcup/bin

###################################################

RUN git clone https://github.com/jyp/prettiest

WORKDIR /workspace/prettiest

# 5e7a12cf37bb01467485bbe1e9d8f272fa4f8cd5 is the camera-ready version
# of Bernardy's printer

ARG BERNARDY_PRINTER_COMMIT=5e7a12cf37bb01467485bbe1e9d8f272fa4f8cd5

RUN git checkout $BERNARDY_PRINTER_COMMIT

###################################################

WORKDIR /workspace

RUN cabal install --lib \
    base-compat-0.12.2 \
    optparse-applicative-0.17.0.0 \
    criterion-1.6.0.0 \
    aeson-2.1.2.1 \
    attoparsec-0.14.4 \
    wl-pprint-1.2.1

###################################################
# Install elan + lean

RUN curl -O https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
RUN chmod +x elan-init.sh
RUN ./elan-init.sh -y --default-toolchain "leanprover/lean4:nightly-2023-02-23"
RUN rm elan-init.sh
ENV PATH=${PATH}:/root/.elan/bin

COPY lean/ lean
WORKDIR /workspace/lean



# <--- This is the last computationally intensive task.
#      If not necessary, don't invalidate the cache.
#      On the other hand, if we will edit stuff above,
#      make sure to clean all things up!

# COPY other-artifacts/ other-artifacts
# WORKDIR /workspace/other-artifacts

# RUN cp -r ../prettiest/Text Text
# COPY bernardy-remove-width-limit.patch .
# RUN patch -p1 < bernardy-remove-width-limit.patch
# RUN mv Text TextPatched

# RUN cp -r ../prettiest/Text Text

# RUN cabal build
