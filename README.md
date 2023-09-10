# Overview of "A Pretty Expressive Printer"

This is the artifact for the OOPSLA 2023 paper "A Pretty Expressive Printer"

NOTE: the artifact's initial version that was submitted for artifact evaluation can be found at 
https://github.com/sorawee/pretty-expressive-oopsla23-artifact/releases/tag/artifact-eval.
The paper's title was initially "An expressive and optimal pretty printer", 
and the implementation was initially named "SnowWhite".

## Table of contents

- [Introduction](#introduction)
  - [Formalization and proofs](#formalization-and-proofs)
  - [Implementations](#implementations)
  - [Evaluation](#evaluation)
- [Getting Started Guide](#getting-started-guide)
  - [Hardware requirements](#hardware-requirements)
  - [Installation](#installation)
  - [Basic testing](#basic-testing)
- [Step-by-Step Instructions](#step-by-step-instructions)
  - [Evaluation: Lean formalization](#evaluation-lean-formalization)
  - [Evaluation: Rosette proof](#evaluation-rosette-proof)
  - [Evaluation: benchmarks](#evaluation-benchmarks)
  - [Evaluation: implementations](#evaluation-implementations)
- [Additional information](#additional-information)
  - [Documentation](#documentation)

## Introduction 

Our paper introduced a pretty printer that is expressive, optimal, and practically efficient. 
The pretty printer is formalized and proven correct in the Lean theorem prover. 
We implemented the pretty printer in OCaml and Racket, which is called PrettyExpressive 
(`pretty-expressive` in this artifact).
We further created a code formatter for Racket (for formatting Racket source code), 
powered by the Racket PrettyExpressive. 
To evaluate our pretty printer, we run experiments on our benchmarks to show that 
PrettyExpressive is practically efficient and produces layouts with high quality.
The artifact supports the paper by providing the Lean formalization, implementations, 
and benchmarks to reproduce the evaluation.

The following elaborates all claims made in the paper.

### Formalization and proofs

All proofs in this paper are either 

- formalized in Lean theorem prover 
- sketched in the paper's Appendix B
- proven with automated theorem proving via Rosette/Z3

In particular, the correctness proofs are formalized in Lean, and included in the artifact
under the directory `/workspace/lean/Pretty`.

| Definition / Theorem                                     | Paper       | File                           | Name in Lean                                                              | Notation in paper                                 |
|----------------------------------------------------------|-------------|--------------------------------|---------------------------------------------------------------------------|---------------------------------------------------|
| Document definition                                      | Figure 4    | `Defs/Basic.lean`              | `Doc`                                                                     | Syntax of $\Sigma_e$                              |
| Choiceless document definition                           | Section 3.1 | `Defs/Basic.lean`              | `Choiceless`                                                              |                                                   |
| Cost factory interface definition                        | Figure 6    | `Defs/Factory.lean`            | `Factory`                                                                 |                                                   |
| Cost function definition                                 | Section 3.2 | `Defs/Basic.Lean`              | `Layout.find_cost`                                                        | `Cost`                                            |
| Layout definition                                        | Section 4.1 | `Defs/Layout.lean`             | `Layout`                                                                  |                                                   |
| Rendering relation definition                            | Figure 8    | `Defs/Basic.lean`              | `Render`                                                                  | $\Downarrow_{\mathcal{R}}$                        |
| Widening relation definition                             | Figure 8    | `Defs/Basic.lean`              | `Widen`                                                                   | $\Downarrow_{\mathcal{W}}$                        |
| Determinism and totality of rendering theorems           | Section 4.2 | `Claims/Render.lean`           | `Render_deterministic`<br>`Render_total`                                  |                                                   |
| Determinism and totality of widening theorems            | Section 4.2 | `Claims/Widen.lean`            | `Widen_deterministic`<br>`Widen_total`                                    |                                                   |
| Measure definition                                       | Figure 12   | `Defs/Basic.lean`              | `Meas`                                                                    |                                                   |
| Measure operation definitions                            | Figure 12   | `Defs/Basic.lean`              | `Meas.adjust_align`<br>`Meas.adjust_nest`<br>`Meas.concat`<br>`dominates` | `alignLift`<br>`nestLift`<br>$\circ$<br>$\preceq$ |
| Measure computation/rendering relation definition        | Figure 13   | `Defs/Basic.lean`              | `MeasRender`                                                              | $\Downarrow_{\mathbb{M}}$                         |
| Determinism and totality of measure computation theorems | Section 6.2 | `Claims/MeasRender.lean`       | `MeasRender_deterministic`<br>`MeasRender_total`                          |                                                   |
| Measure computation correctness theorem(s)               | Theorem 6.2 | `Claims/MeasRender.lean`       | `MeasRender_single_correct`<br>`MeasRender_multi_correct`                 |                                                   |
| Measure set definition                                   | Figure 14   | `Defs/Basic.lean`              | `MeasureSet`                                                              |                                                   |
| List of measures operation definitions                   | Figure 14   | `Defs/Basic.lean`              | `dedup`<br>`merge`                                                        | `dedup`<br>$\uplus$                               |
| Measure set operation definitions                        | Figure 14   | `Defs/MeasureSetOps.lean`      | `MeasureSet.lift`<br>`MeasureSet.taint`<br>`MeasureSet.union`             | `lift`<br>`taint`<br>$\uplus$                     |
| Resolving relation definition                            | Figure 15   | `Defs/Resolve.lean`            | `Resolve`                                                                 | $\Downarrow_{\mathbb{RS}}$                        |
| Determinism of resolving theorem                         | Section 6.5 | `Claims/ResolveDet.lean`       | `Resolve_deterministic`                                                   |                                                   |
| Totality of resolving theorem                            | Section 6.5 | `Claims/ResolveTotal.lean`     | `Resolve_total`                                                           |                                                   |
| Optimality of resolving theorem                          | Theorem 6.6 | `Claims/ResolveOptimal.lean`   | `Resolve_optimal`                                                         |                                                   |
| Validity of resolving theorems                           | Theorem 6.7 | `Claims/ResolveValid.lean`     | `Resolve_valid`<br>`Resolve_tainted_valid`                                |                                                   |
| Measure set size bound lemma                             | Lemma 6.8   | `Claims/ResolveEfficient.lean` | `Resolve_bound`                                                           |                                                   |
| Taintedness when resolving exceeds the limit             | Lemma 6.9   | `Claims/ResolveEfficient.lean` | `Resolve_exceeding_tainted`                                               |                                                   |

The dependency graph of Lean files can be accessed at `/workspace/lean/import_graph.png`

(Non-)conformance of various cost factories (Definition 3.4, 3.5, 3.6, 3.8) to the cost factory interface (Theorem 3.7) 
is proven using automated theorem proving, via Rosette and Z3 (`/workspace/rosette/cost-factory.rkt`).

Other proofs (those in Section 5 and the main time complexity analysis) are sketched in Appendix B of the paper.

### Implementations 

As described in Section 6, we implemented PrettyExpressive in both OCaml and Racket,
and implemented a code formatter for Racket code using the Racket version of
PrettyExpressive. The artifact contains all three implementations:

| Name                                   | Path                                         |
|----------------------------------------|----------------------------------------------|
| OCaml PrettyExpressive pretty printer  | `/workspace/pretty-expressive-ocaml/pretty/` |
| Racket PrettyExpressive pretty printer | `/workspace/pretty-expressive-racket/`       |
| Racket code formatter                  | `/workspace/fmt/`                            |

### Evaluation 

In Section 7, we claim that PrettyExpressive runs fast in practice and 
produces pretty layouts. These claims are backed by two experiments:

- The first experiment compares the OCaml PrettyExpressive against other popular pretty printers 
  (Bernardy's and Wadler/Leijen's pretty printer) on a set of benchmarks. 
  The description of the benchmarks can be found in Section 7.1.
- The second experiment runs the Racket code formatter to evaluate its performance and quality 
  on another set of benchmarks.
  The description of the benchmarks can be found in Section 7.2.

Table 2 and Table 3 detail the results of these experiments, 
and Section 7.3 explains how they support the claims.

This artifact contains the benchmarks and scripts to reproduce both tables.

## Getting Started Guide 

### Hardware requirements

To use this artifact, you will need a machine capable of running Docker with at least 15 GB of free disk space. 

For reference, we tested this artifact on an Apple M1 Macbook Pro with 16GB of RAM 
and Linux x86-64 with 16GB of RAM. 
The performance results you obtain may vary from ours because of the lack of Dockerization in our run, 
and they may depend on your particular machine setup, including CPU, available RAM, concurrently running processes, etc. 
However, we do expect the _relative_ performance on the benchmarks to be approximately the same.

### Installation

The only required installation is Docker. See https://docs.docker.com/install/ for details on how to install Docker.

After installing Docker, you can download and run the Docker image.

If you have an AArch64 machine (Mac M1 or M2), run (possibly with `sudo` if required):

```
# Download image (~15 GB download). 
$ docker pull soraweep/pretty-expressive-oopsla23-artifact:latest-aarch64
$ docker run -it --name pretty-artifact soraweep/pretty-expressive-oopsla23-artifact:latest-aarch64
```

If you have an x86-64 machine, run (possibly with `sudo` if required):

```
# Download image (~15 GB download). 
$ docker pull soraweep/pretty-expressive-oopsla23-artifact:latest-amd64
$ docker run -it --name pretty-artifact soraweep/pretty-expressive-oopsla23-artifact:latest-amd64
```

This will drop you into a shell inside the container, in the `/workspace` directory, the main directory containing Lean proofs, implementations, and benchmarks.

We have installed `vim` into the container for convenience to edit and view files; you can also use Docker to copy files into and out of the container, see <https://docs.docker.com/engine/reference/commandline/cp/>.

If you leave the container and wish to get back, you will need to restart it with the command `docker start -ia pretty-artifact`. If you wish to instead start from a fresh copy of the image, run `docker rm pretty-artifact` to remove the container and then follow the instructions for the first run of the container above.

### Basic testing

#### Sanity test: Lean formalization 

(Expected execution time: ~1 minute)

To test that Lean can check our proofs, run the following commands:

```
$ cd /workspace/lean 
$ racket scripts/gen-main.rkt  # generate main file
$ lake build                   # build our project
```

This should compile all of our Lean files under the directory `Pretty` with no errors.

#### Sanity test: Rosette proof 

(Expected execution time: ~1 minute)

To test that Rosette can prove about the conformance of cost factories  
to the cost factory interface, run:

```
$ cd /workspace/rosette 
$ racket cost-factory.rkt
```

which should contain:

```
== pretty-expressive factory ==

<= - transitivity: verified

<= - antisymmetry: verified

<= - total: verified

+ - translational invariance: verified

+ - associativity: verified

text - ordered: verified

text - additive: verified

text - id left: verified

text - id right: verified

nl - ordered: verified
```

#### Sanity test: implementations

(Expected execution time: instant)

To test that our OCaml PrettyExpressive implementation is functional, run the following commands:

```
$ cd /workspace/pretty-expressive-ocaml
$ ./run.sh examples/fig_1.ml
```

To test that our Racket PrettyExpressive implementation is functional, run the following commands:

```
$ cd /workspace/pretty-expressive-racket 
$ racket examples.rkt
```

Both runs should produce the same output:

```
function append(first,second,third){
    return first +
        second +
        third
}
function append(first,second,third){
    return (
        first +
        second +
        third
    )
}
function append(first,second,third){
    return (
        first +
        second +
        third
    )
}
function append(first,second,third){
    return first + second + third
}
function append(first,second,third){
    return first + second + third
}
function append(first,second,third){
    return first + second + third
}
```

To test that our Racket code formatter is functional, run the following commands:

```
$ cd /workspace/fmt 
$ raco fmt tests/test-cases/define-match.rkt
```

This should produce the following output:

```
#lang racket

(define/match (replace-inst lst1 lst2)
  [('() lst) (cons lst1 lst2)])

(replace-inst '() '(1 2))
```

#### Sanity test: benchmarks

(Expected execution time: ~15 seconds)

To test that our benchmarks are functional, run the following commands:

```
$ cd /workspace
$ racket scripts/gen-table-2.rkt jsonw
$ racket scripts/gen-table-3.rkt list.rkt
```

These commands generate data points for Table 2 and 3 in the directory `benchmark-results`.
You can then view a partially populated table that aggregates these data points with the following command:

```
$ racket scripts/view-tables.rkt
```

This should produce the following output (although the timing information will depend on your machine):

```
┌────────────┬────────────────────────────┬───────────────────────────┬───────────────────┬────────────────┬────────────────────┐
│Benchmark ID│PrettyExpressive (default W)│PrettyExpressive (W = 1000)│Wadler/Leijen      │Bernardy (Naive)│Bernardy (Practical)│
├────────────┼────────────────────────────┼───────────────────────────┼───────────────────┼────────────────┼────────────────────┤
│concat10k   │Unavailable                 │Unavailable                │Unavailable        │Unavailable     │Unavailable         │
├────────────┼────────────────────────────┼───────────────────────────┼───────────────────┼────────────────┼────────────────────┤
... elided ...
├────────────┼────────────────────────────┼───────────────────────────┼───────────────────┼────────────────┼────────────────────┤
│json10k     │Unavailable                 │Unavailable                │Unavailable        │Unavailable     │Unavailable         │
├────────────┼────────────────────────────┼───────────────────────────┼───────────────────┼────────────────┼────────────────────┤
│jsonw       │  0.001 s |    721 | ✗      │  0.001 s |    721 | ✓     │  0.004 s |    721 │5 N/A           │  0.007 s |    709  │
└────────────┴────────────────────────────┴───────────────────────────┴───────────────────┴────────────────┴────────────────────┘

┌──────────────────┬───────────────────────┬───────────────────────┐
│Benchmark ID      │W = 100                │W = 1000               │
├──────────────────┼───────────────────────┼───────────────────────┤
│class-internal.rkt│Unavailable            │Unavailable            │
├──────────────────┼───────────────────────┼───────────────────────┤
│xform.rkt         │Unavailable            │Unavailable            │
├──────────────────┼───────────────────────┼───────────────────────┤
│list.rkt          │  0.030 s |    993 | ✓ │  0.028 s |    993 | ✓ │
├──────────────────┼───────────────────────┼───────────────────────┤
│hash.rkt          │Unavailable            │Unavailable            │
└──────────────────┴───────────────────────┴───────────────────────┘
```

## Step-by-Step Instructions 

In general, the output related to time duration will not exactly match the paper due to differences in hardware and machine configuration. However, we hope it won't deviate significantly, and that the data you obtain will maintain relative order with respect to other data points. For example, if a table in the paper indicates that that PrettyExpressive is significantly faster than Wadler/Leijen's pretty printer in a particular benchmark, this should still hold in your run too, even though the measured times will not exactly match.

### Evaluation: Lean formalization 

(Expected execution time: instant -- proofs are already checked)

Our sanity test has already verified that our Lean proofs are valid. 
You may run it again if you wish:

```
$ cd /workspace/lean 
$ racket scripts/gen-main.rkt  # generate main file
$ lake build                   # build our project
```

You should additionally view the files under the `Pretty` subdirectory
and see that they match the paper's definitions and theorems.
The correspondence is given in the table at [Formalization and proofs](#formalization-and-proofs).
**Three main deviations** from the paper are 

1. The definition of document (`Doc`), which does not contain the `flatten` construct. 
   This is becaused the construct is already dealt in a preprocessing pass, 
   as explained in Section 6.7 (and also Section 6.2) of the paper.
   Also, the document definition additionally contains the `reset` construct, 
   which is explained in Appendix C.
2. The cost factory interface, which generalizes `nl_F` to be a function.
   This is explained in Section 7 of the paper.
   Also, computation width limit is a part of cost factory, 
   since these two arguments are usually set together.
3. The definition of layout, which keeps track of indentation space.
   This is similarly explained in Section 7 of the paper.

### Evaluation: Rosette proof 

(Expected execution time: ~1 minute)

Our sanity test has already verified that our Rosette proofs are valid. 
You may run it again if you wish:

```
$ cd /workspace/rosette
$ racket cost-factory.rkt
```

You should additionally view the file content to see that it verifies the desired properties.


### Evaluation: benchmarks 

(Expected execution time: ~35 minutes)

This section aims to reproduce/generate Table 2 and 3.

First, clear any existing data points.

```
cd /workspace 
rm benchmark-results/*.dat 
```

To generate data points for Table 2, run:

```
racket scripts/gen-table-2.rkt
```

To generate data points for Table 3, run:

```
racket scripts/gen-table-3.rkt
```

As mentioned earlier, both scripts will create `.dat` files under the `benchmark-results` directory.
By default, the scripts will generate 5 data points. 
The number of generated data points can be controlled by the `--iter` option.
Run `racket scripts/gen-table-3.rkt --help` for more details.

The tables can then be viewed with:

```
$ racket scripts/view-tables.rkt
```

You should verify that the output is consistent with that of Table 2 and 3 in the paper. In particular:

- The line counts should match those in the paper.
- The "Timeout" and "N/A" statuses should match those in the paper.
- The relative timings should generally match those in the paper.

### Evaluation: implementations 

(Expected execution time: instant)

You should run the example files that were described in the sanity test again. That is:

```
$ cd /workspace/pretty-expressive-ocaml
$ ./run.sh examples/fig_1.ml
```

and

```
$ cd /workspace/pretty-expressive-racket 
$ racket examples.rkt
```

Both should produce the same output, and the output should match (in order):

- the first layout of Figure 1a
- the first layout of Figure 1b
- the first layout of Figure 1b (again)
- the second layout of Figure 1a
- the second layout of Figure 1b
- the second layout of Figure 1b (again)

You are free to modify `fig_1.ml` and `examples.rkt` 
to validate that the implementations work on other inputs.

Similarly, feel free to format Racket files under `/workspace/fmt/tests`, 
or any other Racket files with `raco fmt <filename.rkt>`.
Code formatting should work on all Racket files that can be successfully parsed.

The implementation should match well to the formalism in the paper.
Deviations are documented in Section 7 and Appendix C.
Also, computation width limit is a part of cost factory, 
since these two arguments are usually set together.

## Additional information 

### Documentation 

All implementations and Lean formalization are documented via the recommended format for their ecosystems.
For the Racket PrettyExpressive and Racket code formatter, the documentation is in the Scribble format. 
For the OCaml PrettyExpressive, the documentation is in the OCamldoc format in the interface files (`.mli`). 
For the Lean formalization, the documentation is written in-source. 
Reviewers can read the documentation from these formats directly. 

| System                  | Documentation source path                          |
|-------------------------|----------------------------------------------------|
| OCaml PrettyExpressive  | `/workspace/pretty-expressive-ocaml/printer/`      |
| Racket PrettyExpressive | `/workspace/pretty-expressive-racket/scribblings/` |
| Racket code formatter   | `/workspace/fmt/scribblings/`                      |
| Lean formalization      | `/workspace/lean/Pretty`                           |

Optionally, reviewers can extract HTML documentation via tools in the ecosystem 
(`doc-gen4` for Lean code, `scribble` for Racket code, and `odoc` for OCaml code).
We are aware that these tools do not work in all circumstances 
(e.g. we are unable to run `doc-gen4` in Docker when running on Apple M1),
which is why HTML generation is optional for reviewing.
Regardless, following are the commands to generate the HTML documentation.

```
# OCaml PrettyExpressive
$ cd /workspace/pretty-expressive-ocaml/
$ make doc 
# The rendered documentation is at 
# /workspace/pretty-expressive-ocaml/_build/default/_doc/_html/

# Racket PrettyExpressive documentation is already rendered, which is at
# /workspace/pretty-expressive-racket/doc/

# Racket code formatter documentation is already rendered, which is at
# /workspace/fmt/doc/

# Lean formalization
$ cd /workspace/lean 
$ make doc-setup
$ make doc # This will take a long time, and could fail due to arch mismatch
# The rendered documentation is at /workspace/lean/build/doc/
```

Although not a part of the artifact, these HTML documentations are also online at 

- Lean formalization: https://sorawee.github.io/pretty-expressive-lean/Pretty.html
- OCaml PrettyExpressive: https://sorawee.github.io/pretty-expressive-ocaml/pretty_expressive/Pretty/index.html
- Racket PrettyExpressive: https://docs.racket-lang.org/pretty-expressive/
- Racket code formatter: https://docs.racket-lang.org/fmt/
