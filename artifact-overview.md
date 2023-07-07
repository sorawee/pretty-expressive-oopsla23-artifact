# Overview of "A pretty expressive printer"

This is the artifact for the OOPSLA 2023 paper "A pretty expressive printer"
(previously titled "An expressive and optimal pretty printer").

For non-reviewers: this artifact is for the initially submitted paper
(included in the artifact as `paper-and-appendix.pdf`). 
The camera ready version may have different organization 
(e.g., different section or figure numbering),
causing mismatches between the paper and the artifact.
We will provide an updated artifact that is consistent with the camera ready version, however.

## Table of contents

- [Introduction](#introduction)
- [Getting Started Guide](#getting-started-guide)
  - [Hardware requirements](#hardware-requirements)
  - [Installation](#installation)
  - [Basic testing](#basic-testing)
- [Step-by-Step Instructions](#step-by-step-instructions)
- [Additional information](#additional-information)
  - [Artifact contents](#artifact-contents)

## Introduction 

Our paper introduced a pretty printer that is expressive, optimal, and practically efficient. 
The pretty printer is formalized and proven correct in the Lean theorem prover. 
We implemented the pretty printer in OCaml and Racket. 
These implementations are called SnowWhite in the paper, 
and called `pretty-expressive` in the artifact.
We further created a code formatter for Racket (for formatting Racket source code), 
powered by the Racket SnowWhite. 
To evaluate our pretty printer, we run experiments on our benchmarks to show that 
SnowWhite is practically efficient and produces layouts with high quality.
The artifact supports the paper by providing the Lean formalization, implementations, 
and benchmarks to reproduce the evaluation.

More elaboratedly, following are all claims in the paper.

### Formalization and proofs

All proofs in this paper are either formalized in Lean or sketched in the paper's Appendix B.
In particular, the correctness proofs are formalized in Lean, and included in the artifact
under the directory `/workspace/lean/Pretty`.

| Definition / Theorem                                                      | Paper                | File                           | Name in Lean                                                              | Notation in paper                                 |
|---------------------------------------------------------------------------|----------------------|--------------------------------|---------------------------------------------------------------------------|---------------------------------------------------|
| Layout definition                                                         | Page 7, Section 3.1  | `Defs/Basic.lean`              | `Layout`                                                                  |                                                   |
| Document definition                                                       | Page 7, Figure 4     | `Defs/Basic.lean`              | `Doc`                                                                     | Syntax of $\Sigma_e$                              |
| Choiceless document definition                                            | Page 7, Section 3.2  | `Defs/Basic.lean`              | `Choiceless`                                                              |                                                   |
| Rendering relation definition                                             | Page 9, Figure 6     | `Defs/Basic.lean`              | `Render`                                                                  | $\Downarrow_{\mathcal{R}}$                        |
| Widening relation definition                                              | Page 9, Figure 6     | `Defs/Basic.lean`              | `Widen`                                                                   | $\Downarrow_{\mathcal{W}}$                        |
| Determinism and totality of rendering theorems                            | Page 10, Section 3.3 | `Claims/Render.lean`           | `Render_deterministic`<br>`Render_total`                                  |                                                   |
| Determinism and totality of widening theorems                             | Page 10, Section 3.3 | `Claims/Widen.lean`            | `Widen_deterministic`<br>`Widen_total`                                    |                                                   |
| Cost factory interface definition                                         | Page 14, Figure 8    | `Defs/Factory.lean`            | `Factory`                                                                 |                                                   |
| Measure definition                                                        | Page 16, Figure 10   | `Defs/Basic.lean`              | `Meas`                                                                    |                                                   |
| Measure operation definitions                                             | Page 16, Figure 10   | `Defs/Basic.lean`              | `Meas.adjust_align`<br>`Meas.adjust_nest`<br>`Meas.concat`<br>`dominates` | `alignLift`<br>`nestLift`<br>$\circ$<br>$\preceq$ |
| Measure computation/rendering relation definition                         | Page 16, Figure 11   | `Defs/Basic.lean`              | `MeasRender`                                                              | $\Downarrow_{\mathbb{M}}$                         |
| Determinism and totality of measure computation theorems                  | Page 16, Section 5.3 | `Claims/MeasRender.lean`       | `MeasRender_deterministic`<br>`MeasRender_total`                          |                                                   |
| Measure computation correctness theorem(s)                                | Page 16, Theorem 5.3 | `Claims/MeasRender.lean`       | `MeasRender_single_correct`<br>`MeasRender_multi_correct`                 |                                                   |
| Measure set definition                                                    | Page 17, Figure 12   | `Defs/Basic.lean`              | `MeasureSet`                                                              |                                                   |
| List of measures operation definitions                                    | Page 17, Figure 12   | `Defs/Basic.lean`              | `dedup`<br>`merge`                                                        | `dedup`<br>$\uplus$                               |
| Measure set operation definitions                                         | Page 17, Figure 12   | `Defs/MeasureSetOps.lean`      | `MeasureSet.lift`<br>`MeasureSet.taint`<br>`MeasureSet.union`             | `lift`<br>`taint`<br>$\uplus$                     |
| Resolving relation definition                                             | Page 19, Figure 13   | `Defs/Resolve.lean`            | `Resolve`                                                                 | $\Downarrow_{\mathbb{RS}}$                        |
| Determinism of resolving theorem                                          | Page 19, Section 5.6 | `Claims/ResolveDet.lean`       | `Resolve_deterministic`                                                   |                                                   |
| Totality of resolving theorem                                             | Page 19, Section 5.6 | `Claims/ResolveTotal.lean`     | `Resolve_total`                                                           |                                                   |
| Optimality of resolving theorem                                           | Page 20, Theorem 5.7 | `Claims/ResolveOptimal.lean`   | `Resolve_optimal`                                                         |                                                   |
| Validity of resolving theorems                                            | Page 20, Theorem 5.8 | `Claims/ResolveValid.lean`     | `Resolve_valid`<br>`Resolve_tainted_valid`                                |                                                   |
| Measure set size bound lemma                                              | Page 20, Lemma 5.9   | `Claims/ResolveEfficient.lean` | `Resolve_bound`                                                           |                                                   |
| Taintedness when resolving exceeds the limit                              | Page 20, Lemma 5.10  | `Claims/ResolveEfficient.lean` | `Resolve_exceeding_tainted`                                               |                                                   |
| Conformance of SnowWhite's cost factory to the cost factory interface | Page 20, Section 6   | `Claims/OurFactory.lean`       | `ourFactory`                                                              |                                                   |

Other proofs (those in Section 4 and the main time complexity analysis) are sketched in Appendix B.

### Implementations 

As detailed in Section 6, we implemented the OCaml and Racket SnowWhite,
and then implemented the Racket code formatter which utilizes the Racket SnowWhite as its foundation.
The artifact contains all three implementations.

| Name                            | Path                                  |
|---------------------------------|---------------------------------------|
| OCaml SnowWhite pretty printer  | `/workspace/pretty-expressive-ocaml`  |
| Racket SnowWhite pretty printer | `/workspace/pretty-expressive-racket` |
| Racket code formatter           | `/workspace/fmt`                      |

### Evaluation 

In Section 7, we claimed that:

1. SnowWhite runs fast in practice
2. SnowWhite produces pretty layouts in practice

These claims are backed by two experiments. 

The first experiment compares OCaml SnowWhite against other popular pretty printers 
(Bernardy's and Wadler/Leijen's pretty printer) on a set of benchmarks. 
The description on each benchmark can be found in Section 7.1.

The second experiment runs the Racket code formatter to evaluate its performance and quality 
on another set of benchmarks.

Table 2 and Table 3 detail the results of these experiment, 
and Section 7.3 explains how they support the claims.
This artifact contains the benchmarks and scripts to reproduce both tables.


## Getting Started Guide 

### Hardware requirements

To use this artifact, you will need a machine capable of running Docker with at least TODO(sorawee)GB of free disk space, and at least TODO(sorawee)GB of RAM. 

For reference, we tested this artifact on an Apple M1 Macbook Pro with 16GB of RAM. 
The performance results you obtain may vary from ours because of the lack of Dockerization in our run, 
and they may depend on your particular machine setup, including CPU, available RAM, concurrently running processes, etc. 
However, we do expect relative performance on the benchmarks to be approximately the same.

### Installation

The only required installation is Docker. See https://docs.docker.com/install/ for details on how to install Docker.

After installing Docker, you can download and run the Docker image by running:

```
# Download image (~TODO(sorawee) GB download)
$ docker pull unsat/pretty-expressive-oopsla23-artifact:latest

# Run the image
$ docker run -it --name pretty-expressive-artifact unsat/pretty-expressive-oopsla23-artifact:latest
```

This will drop you into a shell inside the container, in the `/workspace` directory, the main directory containing Lean proofs, implementations, and benchmarks.

We have installed `vim` into the container for convenience to edit and view files; you can also use Docker to copy files into and out of the container, see <https://docs.docker.com/engine/reference/commandline/cp/>.

If you leave the container and wish to get back, you will need to restart it with the command `docker start -ia pretty-expressive-artifact`. If you wish to instead start from a fresh copy of the image, run `docker rm pretty-expressive-artifact` to remove the container and then follow the instructions for the first run of the container above.

### Basic testing


#### Sanity test: Lean formalization 

Run the following commands:

```
$ cd /workspace/lean 
$ lake clean 
$ lake build
```

This should produce exactly one error:

```
./././Pretty/Bad.lean:5:31: error: unsolved goals
⊢ False
```

All other files should be built without any error.

#### Sanity test: implementations

#### Sanity test: benchmarks


## Step-by-Step Instructions 


### Evaluation: comparison of pretty printers 

| Benchmark ID | Benchmarks                                     | Available targets                                                                                     |
|-------------------|------------------------------------------------|-------------------------------------------------------------------------------------------------------|
| `concat`          | Concat10k, Concat50k                           | `pretty-expressive`, `leijen`, `bernardy-patched`                                                     |
| `fill-sep`        | FillSep5k, FillSep50k                          | `pretty-expressive`, `leijen`, `bernardy-paper`, `bernardy-patched`                                   |
| `flatten`         | Flatten8k, Flatten16k                          | `pretty-expressive`, `leijen`                                                                         |
| `sexp-full`       | SExpFull15, SExpFull16                         | `pretty-expressive`, `leijen`, `bernardy-paper`, `bernardy-patched`                                   |
| `sexp-random`     | RandFit1k, RandFit10k, RandOver1k, RandOver10k | `pretty-expressive`, `leijen`, `bernardy-paper` (failing for RandOver benchmarks), `bernardy-patched` |
| `json`            | JSON1k, JSON10k, JSONW                         | `pretty-expressive`, `leijen`, `bernardy-patched`                                                     |


### Evaluation: Racket code formatter 

Table 3 details the results of this experiment. 
Likewise, .

| Benchmark   | Commands                                                                                                                   |
|-------------|----------------------------------------------------------------------------------------------------------------------------|
| Concat10k   | `racket table-2.rkt --benchmark concat --size 10000 --page-width 80 --target pretty-expressive --computation-width 100`    |
|             | `racket table-2.rkt --benchmark concat --size 10000 --page-width 80 --target pretty-expressive --computation-width 1000`   |
|             | `racket table-2.rkt --benchmark concat --size 10000 --page-width 80 --target wadler `                                      |
|             | `racket table-2.rkt --benchmark concat --size 10000 --page-width 80 --target bernardy-patched `                            |
| Concat50k   | `racket table-2.rkt --benchmark concat --size 50000 --page-width 80 --target pretty-expressive --computation-width 100`    |
|             | `racket table-2.rkt --benchmark concat --size 50000 --page-width 80 --target pretty-expressive --computation-width 1000`   |
|             | `racket table-2.rkt --benchmark concat --size 50000 --page-width 80 --target wadler `                                      |
|             | `racket table-2.rkt --benchmark concat --size 50000 --page-width 80 --target bernardy-patched `                            |
| FillSep5k   | `racket table-2.rkt --benchmark fill-sep --size 5000 --page-width 80 --target pretty-expressive --computation-width 100`   |
|             | `racket table-2.rkt --benchmark fill-sep --size 5000 --page-width 80 --target pretty-expressive --computation-width 1000`  |
|             | `racket table-2.rkt --benchmark fill-sep --size 5000 --page-width 80 --target wadler `                                     |
|             | `racket table-2.rkt --benchmark fill-sep --size 5000 --page-width 80 --target bernardy-paper `                             |
|             | `racket table-2.rkt --benchmark fill-sep --size 5000 --page-width 80 --target bernardy-patched `                           |
| FillSep50k  | `racket table-2.rkt --benchmark fill-sep --size 50000 --page-width 80 --target pretty-expressive --computation-width 100`  |
|             | `racket table-2.rkt --benchmark fill-sep --size 50000 --page-width 80 --target pretty-expressive --computation-width 1000` |
|             | `racket table-2.rkt --benchmark fill-sep --size 50000 --page-width 80 --target wadler `                                    |
|             | `racket table-2.rkt --benchmark fill-sep --size 50000 --page-width 80 --target bernardy-paper `                            |
|             | `racket table-2.rkt --benchmark fill-sep --size 50000 --page-width 80 --target bernardy-patched `                          |
| Flatten8k   | `racket table-2.rkt --benchmark flatten --size 8000 --page-width 80 --target pretty-expressive --computation-width 100`    |
|             | `racket table-2.rkt --benchmark flatten --size 8000 --page-width 80 --target pretty-expressive --computation-width 1000`   |
|             | `racket table-2.rkt --benchmark flatten --size 8000 --page-width 80 --target wadler `                                      |
| Flatten16k  | `racket table-2.rkt --benchmark flatten --size 16000 --page-width 80 --target pretty-expressive --computation-width 100`   |
|             | `racket table-2.rkt --benchmark flatten --size 16000 --page-width 80 --target pretty-expressive --computation-width 1000`  |
|             | `racket table-2.rkt --benchmark flatten --size 16000 --page-width 80 --target wadler `                                     |
| SExpFull15  | `racket table-2.rkt --benchmark sexp-full --size 15 --page-width 80 --target pretty-expressive --computation-width 100`    |
|             | `racket table-2.rkt --benchmark sexp-full --size 15 --page-width 80 --target pretty-expressive --computation-width 1000`   |
|             | `racket table-2.rkt --benchmark sexp-full --size 15 --page-width 80 --target wadler`                                       |
|             | `racket table-2.rkt --benchmark sexp-full --size 15 --page-width 80 --target bernardy-paper`                               |
|             | `racket table-2.rkt --benchmark sexp-full --size 15 --page-width 80 --target bernardy-patched`                             |
| SExpFull16  | `racket table-2.rkt --benchmark sexp-full --size 16 --page-width 80 --target pretty-expressive --computation-width 100`    |
|             | `racket table-2.rkt --benchmark sexp-full --size 16 --page-width 80 --target pretty-expressive --computation-width 1000`   |
|             | `racket table-2.rkt --benchmark sexp-full --size 16 --page-width 80 --target wadler`                                       |
|             | `racket table-2.rkt --benchmark sexp-full --size 16 --page-width 80 --target bernardy-paper`                               |
|             | `racket table-2.rkt --benchmark sexp-full --size 16 --page-width 80 --target bernardy-patched`                             |
| RandFit1k   | `racket table-2.rkt --benchmark sexp-random --size 1 --page-width 80 --target pretty-expressive --computation-width 100`   |
|             | `racket table-2.rkt --benchmark sexp-random --size 1 --page-width 80 --target pretty-expressive --computation-width 1000`  |
|             | `racket table-2.rkt --benchmark sexp-random --size 1 --page-width 80 --target wadler`                                      |
|             | `racket table-2.rkt --benchmark sexp-random --size 1 --page-width 80 --target bernardy-paper`                              |
|             | `racket table-2.rkt --benchmark sexp-random --size 1 --page-width 80 --target bernardy-patched`                            |
| RandFit1k   | `racket table-2.rkt --benchmark sexp-random --size 2 --page-width 80 --target pretty-expressive --computation-width 100`   |
|             | `racket table-2.rkt --benchmark sexp-random --size 2 --page-width 80 --target pretty-expressive --computation-width 1000`  |
|             | `racket table-2.rkt --benchmark sexp-random --size 2 --page-width 80 --target wadler`                                      |
|             | `racket table-2.rkt --benchmark sexp-random --size 2 --page-width 80 --target bernardy-paper`                              |
|             | `racket table-2.rkt --benchmark sexp-random --size 2 --page-width 80 --target bernardy-patched`                            |
| RandOver1k  | `racket table-2.rkt --benchmark sexp-random --size 3 --page-width 80 --target pretty-expressive --computation-width 100`   |
|             | `racket table-2.rkt --benchmark sexp-random --size 3 --page-width 80 --target pretty-expressive --computation-width 1000`  |
|             | `racket table-2.rkt --benchmark sexp-random --size 3 --page-width 80 --target wadler`                                      |
|             | `racket table-2.rkt --benchmark sexp-random --size 3 --page-width 80 --target bernardy-patched`                            |
| RandOver10k | `racket table-2.rkt --benchmark sexp-random --size 4 --page-width 80 --target pretty-expressive --computation-width 100`   |
|             | `racket table-2.rkt --benchmark sexp-random --size 4 --page-width 80 --target pretty-expressive --computation-width 1000`  |
|             | `racket table-2.rkt --benchmark sexp-random --size 4 --page-width 80 --target wadler`                                      |
|             | `racket table-2.rkt --benchmark sexp-random --size 4 --page-width 80 --target bernardy-patched`                            |
| JSON1k      | `racket table-2.rkt --benchmark json --size 1 --page-width 80 --target pretty-expressive --computation-width 100`          |
|             | `racket table-2.rkt --benchmark json --size 1 --page-width 80 --target pretty-expressive --computation-width 1000`         |
|             | `racket table-2.rkt --benchmark json --size 1 --page-width 80 --target wadler`                                             |
|             | `racket table-2.rkt --benchmark json --size 1 --page-width 80 --target bernardy-patched`                                   |
| JSON10k     | `racket table-2.rkt --benchmark json --size 2 --page-width 80 --target pretty-expressive --computation-width 100`          |
|             | `racket table-2.rkt --benchmark json --size 2 --page-width 80 --target pretty-expressive --computation-width 1000`         |
|             | `racket table-2.rkt --benchmark json --size 2 --page-width 80 --target wadler`                                             |
|             | `racket table-2.rkt --benchmark json --size 2 --page-width 80 --target bernardy-patched`                                   |
| JSONW       | `racket table-2.rkt --benchmark json --size 1 --page-width 50 --target pretty-expressive --computation-width 60`           |
|             | `racket table-2.rkt --benchmark json --size 1 --page-width 50 --target pretty-expressive --computation-width 1000`         |
|             | `racket table-2.rkt --benchmark json --size 1 --page-width 50 --target wadler`                                             |
|             | `racket table-2.rkt --benchmark json --size 1 --page-width 50 --target bernardy-patched`                                   |

## Additional information 

### Artifact contents
