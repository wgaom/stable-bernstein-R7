# Stable Bernstein in R⁷: algebraic verification

This repository contains Lean and Mathematica implementations verifying the algebraic estimates needed in the paper on the stable Bernstein theorem in R⁷.

## Files to read

- [`lean/R7/Definitions.lean`](lean/R7/Definitions.lean): parameters and definitions.
- [`lean/R7/Theorems.lean`](lean/R7/Theorems.lean): the two estimates, `R7.Paper.scalar_bound` and `R7.Paper.spectral_bound`.
- [`mathematica/Verification.nb`](mathematica/Verification.nb): definitions and exact verification in Mathematica.

The remaining Lean files contain the proofs and exact rational certificates, grouped under `Algebra/`, `Scalar/`, `Spectral/`, and `Certificates/`.

## Lean

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/wgaom/stable-bernstein-R7.git
cd stable-bernstein-R7/lean
lake exe cache get
lake build
```

`lake exe cache get` downloads precompiled mathlib dependencies; omit it to build them from source.

Use `LEAN_NUM_THREADS=13 lake build` to set the number of concurrent build jobs.

A successful build checks both theorem proofs and prints their axiom dependencies. Each must contain only `propext`, `Classical.choice`, and `Quot.sound`. The certificates are checked by the Lean kernel.

## Mathematica

Open [`mathematica/Verification.nb`](mathematica/Verification.nb) in Mathematica and select **Evaluation → Evaluate Notebook**.

The notebook reports `PASS` when each estimate is successfully verified.
