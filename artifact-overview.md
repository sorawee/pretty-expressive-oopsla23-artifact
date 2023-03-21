# Overview of "A pretty expressive printer"

This is the artifact for the OOPSLA 2023 paper "A pretty expressive printer"
(previously titled "An expressive and optimal pretty printer").

For non-reviewers: this artifact is for the initially submitted paper
(included in the artifact under the `pdf` directory). 
The camera ready version may have different organization 
(e.g., different section or figure numbering),
causing mismatches between the paper and the artifact.
We will provide an updated artifact that is consistent with the camera ready
paper at <https://github.com/sorawee/pretty-expressive-oopsla23-artifact>.

## Table of contents

- [Introduction](#introduction)
  - [Formalization and proofs](#formalization-and-proofs)
- [Getting Started Guide](#getting-started-guide)
  - [Hardware requirements](#hardware-requirements)
  - [Installation](#installation)
  - [Basic testing](#basic-testing)
- [Step-by-Step Instructions](#step-by-step-instructions)
- [Additional information](#additional-information)
  - [Documentation](#documentation)

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

The following elaborates all claims made in the paper.

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

Other proofs (those in Section 4 and the main time complexity analysis) are sketched in Appendix B of the paper.

### Implementations 

As described in Section 6, we implemented SnowWhite in both OCaml and Racket,
and implemented a code formatter for Racket code using the Racket version of
SnowWhite. The artifact contains all three implementations:

| Name                            | Path                                         |
|---------------------------------|----------------------------------------------|
| OCaml SnowWhite pretty printer  | `/workspace/pretty-expressive-ocaml/pretty/` |
| Racket SnowWhite pretty printer | `/workspace/pretty-expressive-racket/`       |
| Racket code formatter           | `/workspace/fmt/`                            |

### Evaluation 

In Section 7, we claim that SnowWhite runs fast in practice and 
produces pretty layouts. These claims are backed by two experiments:

- The first experiment compares the OCaml SnowWhite against other popular pretty printers 
  (Bernardy's and Wadler/Leijen's pretty printer) on a set of benchmarks. 
  The description of the benchmarks can be found in Section 7.1.
- The second experiment runs the Racket code formatter to evaluate its performance and quality 
  on another set of benchmarks.
  The description of the benchmarks can be found in Section 7.2.

Table 2 and Table 3 detail the results of these experiments, 
and Section 7.3 explains how they support the claims.

This artifact contains the benchmarks and scripts to reproduce both tables.
**There is a typo in the paper on Table 3, where the line count "5749" should have been "5751".**
All other line counts should match. 
Our corrected Table 3 however still supports the two claims, 
and our interpretation of the results in Section 7.3 still holds for the corrected table.

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
$ lake clean 
$ lake build
```

This should compile all of our Lean files under the directory `Pretty` with no errors.

#### Sanity test: implementations

(Expected execution time: instant)

To test that our OCaml SnowWhite implementation is functional, run the following commands:

```
$ cd /workspace/pretty-expressive-ocaml
$ ./run.sh examples/fig_1.ml
```

To test that our Racket SnowWhite implementation is functional, run the following commands:

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
┌────────────┬──────────────────────────┬──────────────────────────┬──────────────────────┬────────────────┬──────────────────────┐
│Benchmark ID│SnowWhite (default W)     │SnowWhite (W = 1000)      │Wadler/Leijen         │Bernardy (Naive)│Bernardy (Practical)  │
├────────────┼──────────────────────────┼──────────────────────────┼──────────────────────┼────────────────┼──────────────────────┤
│concat10k   │Unavailable               │Unavailable               │Unavailable           │Unavailable     │Unavailable           │
├────────────┼──────────────────────────┼──────────────────────────┼──────────────────────┼────────────────┼──────────────────────┤
... elided ...
├────────────┼──────────────────────────┼──────────────────────────┼──────────────────────┼────────────────┼──────────────────────┤
│json10k     │Unavailable               │Unavailable               │Unavailable           │Unavailable     │Unavailable           │
├────────────┼──────────────────────────┼──────────────────────────┼──────────────────────┼────────────────┼──────────────────────┤
│jsonw       │  0.001081 s |    721 | ✗ │  0.001275 s |    721 | ✓ │  0.006249 s |    721 │N/A             │  0.006329 s |    709 │
└────────────┴──────────────────────────┴──────────────────────────┴──────────────────────┴────────────────┴──────────────────────┘

┌──────────────────┬──────────────────────────┬──────────────────────────┐
│Benchmark ID      │W = 100                   │W = 1000                  │
├──────────────────┼──────────────────────────┼──────────────────────────┤
│class-internal.rkt│Unavailable               │Unavailable               │
├──────────────────┼──────────────────────────┼──────────────────────────┤
│xform.rkt         │Unavailable               │Unavailable               │
├──────────────────┼──────────────────────────┼──────────────────────────┤
│list.rkt          │  0.061600 s |    993 | ✓ │  0.061400 s |    993 | ✓ │
├──────────────────┼──────────────────────────┼──────────────────────────┤
│hash.rkt          │Unavailable               │Unavailable               │
└──────────────────┴──────────────────────────┴──────────────────────────┘
```

## Step-by-Step Instructions 

In general, the output related to time duration will not exactly match the paper due to differences in hardware and machine configuration. However, we hope it won't deviate significantly, and that the data you obtain will maintain relative order with respect to other data points. For example, if a table in the paper indicates that that SnowWhite is significantly faster than Wadler/Leijen's pretty printer in a particular benchmark, this should still hold in your run too, even though the measured times will not exactly match.

### Evaluation: Lean formalization 

(Expected execution time: 30 seconds)

Our sanity test has already verified that our Lean proofs are valid. 
You may run it again if you wish:

```
$ cd /workspace/lean 
$ lake clean 
$ lake build
```

You should additionally view the files under the `Pretty` subdirectory
and see that they match the paper's definitions and theorems.
The correspondence is given in the table at [Formalization and proofs](#formalization-and-proofs).
The **only deviation** from the paper is the definition of document (`Doc`), 
which does not contain the `flatten` construct. This is becaused our core algorithm 
does not deal with this construct, as mentioned in Page 16, Section 5.3 of the paper.

### Evaluation: benchmarks 

(Expected execution time: 35 mins)

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

- The line counts should match those in the paper (except the `class-internal.rkt` benchmark, 
  as noted [earlier](#Evaluation)).
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

## Additional information 

### Documentation 

All implementations and Lean formalization are documented via the recommended format for their ecosystems.
For the Racket SnowWhite and Racket code formatter, the documentation is in the Scribble format. 
For the OCaml SnowWhite, the documentation is in the OCamldoc format in the interface files (`.mli`). 
For the Lean formalization, the documentation is written in-source. 
Reviewers can read the documentation from these formats directly. 

| System                | Documentation source path                          |
|-----------------------|----------------------------------------------------|
| OCaml SnowWhite       | `/workspace/pretty-expressive-ocaml/printer/`      |
| Racket SnowWhite      | `/workspace/pretty-expressive-racket/scribblings/` |
| Racket code formatter | `/workspace/fmt/scribblings/`                      |
| Lean formalization    | `/workspace/lean/Pretty`                           |

Optionally, reviewers can extract HTML documentation via tools in the ecosystem 
(`doc-gen4` for Lean code, `scribble` for Racket code, and `odoc` for OCaml code).
We are aware that these tools do not work in all circumstances 
(e.g. we are unable to run `doc-gen4` in Docker when running on Appple M1),
which is why HTML generation is optional for reviewing.
Regardless, following are the commands to generate the HTML documentation.

```
# OCaml SnowWhite
$ cd /workspace/pretty-expressive-ocaml/
$ make doc 
# The rendered documentation is at 
#/workspace/pretty-expressive-ocaml/_build/default/_doc/_html/

# Racket SnowWhite documentation is already rendered, which is at
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
- OCaml SnowWhite: https://sorawee.github.io/pretty-expressive-ocaml/pretty_expressive/Pretty/index.html
- Racket SnowWhite: https://docs.racket-lang.org/pretty-expressive/
- Racket code formatter: https://docs.racket-lang.org/fmt/
