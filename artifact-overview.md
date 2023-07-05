# Overview of "A pretty expressive printer"

This is the artifact for the OOPSLA 2023 paper "A pretty expressive printer"
(previously titled "An expressive and optimal pretty printer").

For non-reviewers: this artifact is for the initially submitted paper
(included in the artifact). The camera ready version may have different organization,
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

Our paper introduces a pretty printer that is expressive, optimal, and practically efficient. 
The pretty printer is formalized and proven correct in the Lean theorem prover. 
We implement the pretty printer in OCaml and Racket that we call SnowWhite, 
and create a Racket code formatter that utilizes the Racket SnowWhite. 
Furthermore, we run experiments on our benchmarks to show that the OCaml SnowWhite is practically efficient 
relative to other existing pretty printers, and that the Racket code formatter is effective.
The artifact aims to support the paper by providing the implementations, Lean formalization, and benchmarks.

More elaboratedly, following are all claims in the paper.

### Implementations 

There are three implementations in the artifact:

1. OCaml SnowWhite
2. Racket SnowWhite
3. The code formatter for Racket

### Formalization and proofs

All proofs in this paper are either formalized in Lean or sketched in the paper's Appendix B.
We include the Lean formalization (definitions and correctness proofs) in the artifact under 
the directory `/workspace/lean/Pretty`. Following are the descriptions, following the format at 
https://proofartifacts.github.io/guidelines/

| Definition / Theorem                                                          | Paper                | File                           | Name in Lean                                                              | Notation in paper                                 |
|-------------------------------------------------------------------------------|----------------------|--------------------------------|---------------------------------------------------------------------------|---------------------------------------------------|
| Layout definition                                                             | Page 7, Section 3.1  | `Defs/Basic.lean`              | `Layout`                                                                  |                                                   |
| Document definition <br>(syntax of `\Sigma_e`)                                | Page 7, Figure 4     | `Defs/Basic.lean`              | `Doc`                                                                     |                                                   |
| Choiceless document definition                                                | Page 7, Section 3.2  | `Defs/Basic.lean`              | `Choiceless`                                                              |                                                   |
| Rendering relation definition                                                 | Page 9, Figure 6     | `Defs/Basic.lean`              | `Render`                                                                  | $\Downarrow_{\mathcal{R}}$                        |
| Widening relation definition                                                  | Page 9, Figure 6     | `Defs/Basic.lean`              | `Widen`                                                                   | $\Downarrow_{\mathcal{W}}$                        |
| Determinism and totality of <br>rendering theorems                            | Page 10, Section 3.3 | `Claims/Render.lean`           | `Render_deterministic`<br>`Render_total`                                  |                                                   |
| Determinism and totality of <br>widening theorems                             | Page 10, Section 3.3 | `Claims/Widen.lean`            | `Widen_deterministic`<br>`Widen_total`                                    |                                                   |
| Cost factory interface definition                                             | Page 14, Figure 8    | `Defs/Factory.lean`            | `Factory`                                                                 |                                                   |
| Measure definition                                                            | Page 16, Figure 10   | `Defs/Basic.lean`              | `Meas`                                                                    |                                                   |
| Measure operation definitions                                                 | Page 16, Figure 10   | `Defs/Basic.lean`              | `Meas.adjust_align`<br>`Meas.adjust_nest`<br>`Meas.concat`<br>`dominates` | `alignLift`<br>`nestLift`<br>$\circ$<br>$\preceq$ |
| Measure computation/rendering<br>relation definition                          | Page 16, Figure 11   | `Defs/Basic.lean`              | `MeasRender`                                                              | $\Downarrow_{\mathbb{M}}$                         |
| Determinism and totality of <br>measure computation theorems                  | Page 16, Section 5.3 | `Claims/MeasRender.lean`       | `MeasRender_deterministic`<br>`MeasRender_total`                          |                                                   |
| Measure computation <br>correctness theorem(s)                                | Page 16, Theorem 5.3 | `Claims/MeasRender.lean`       | `MeasRender_single_line_correct`<br>`MeasRender_multi_line_correct`       |                                                   |
| Measure set definition                                                        | Page 17, Figure 12   | `Defs/Basic.lean`              | `MeasureSet`                                                              |                                                   |
| Measure set operation definitions<br>(Part 1)                                 | Page 17, Figure 12   | `Defs/Basic.lean`              | `dedup`<br>`merge`                                                        | `dedup`<br>$\uplus$                               |
| Measure set operation definitions<br>(Part 2)                                 | Page 17, Figure 12   | `Defs/MeasureSetOps.lean`      | `MeasureSet.lift`<br>`MeasureSet.taint`<br>`MeasureSet.union`             | `lift`<br>`taint`<br>$\uplus$                     |
| Resolving relation definition                                                 | Page 19, Figure 13   | `Defs/Resolve.lean`            | `Resolve`                                                                 | $\Downarrow_{\mathbb{RS}}$                        |
| Determinism of <br>resolving theorem                                          | Page 19, Section 5.6 | `Claims/ResolveDet.lean`       | `Resolve_deterministic`                                                   |                                                   |
| Totality of <br>resolving theorem                                             | Page 19, Section 5.6 | `Claims/ResolveTotal.lean`     | `Resolve_total`                                                           |                                                   |
| Optimality of resolving theorem                                               | Page 20, Theorem 5.7 | `Claims/ResolveOptimal.lean`   | `Resolve_optimal`                                                         |                                                   |
| Validity of resolving theorems                                                | Page 20, Theorem 5.8 | `Claims/ResolveValid.lean`     | `Resolve_valid`<br>`Resolve_tainted_valid`                                |                                                   |
| Measure set size bound lemma                                                  | Page 20, Lemma 5.9   | `Claims/ResolveBound.lean`     | `Resolve_bound`                                                           |                                                   |
| Taintedness when resolving<br>exceeds the limit                               | Page 20, Lemma 5.10  | `Claims/ResolveExceeding.lean` | `exceeds_tainted`                                                         |                                                   |
| Conformance of SnowWhite's <br>cost factory to <br>the cost factory interface | Page 20, Section 6   | `Claims/OurFactory.lean`       | `ourFactory`                                                              |                                                   |


### Benchmarks

TODO(sorawee)

## Getting Started Guide 

### Hardware requirements

To use this artifact, you will need a machine capable of running Docker with at least TODO(sorawee)GB of free disk space, and at least TODO(sorawee)GB of RAM. 

For reference, we tested this artifact on an Apple M1 Macbook Pro with 16GB of RAM. 
The results you obtain may vary from ours because of the lack of Dockerization in our run, 
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

This will drop you into a shell inside the container, in the `/workspace` directory, the main directory containing Lean proofs and benchmarks.

We have installed `vim` into the container for convenience to edit and view files; you can also use Docker to copy files into and out of the container, see <https://docs.docker.com/engine/reference/commandline/cp/>.

If you leave the container and wish to get back, you will need to restart it with the command `docker start -ia pretty-expressive-artifact`. If you wish to instead start from a fresh copy of the image, run `docker rm pretty-expressive-artifact` to remove the container and then follow the instructions for the first run of the container above.

### Basic testing

#### Sanity test: implementations



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

#### Sanity test: benchmarks


## Step-by-Step Instructions 

## Additional information 

### Artifact contents
