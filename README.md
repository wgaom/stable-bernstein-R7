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

On a fresh clone, omit `lake exe cache get` to build the required mathlib modules from source instead of using their precompiled cache. The R7 proofs are checked in either case.

A successful build checks both theorem proofs and prints their axiom dependencies. Each must contain only `propext`, `Classical.choice`, and `Quot.sound`. The certificates are checked by the Lean kernel.

To compare the formal result with the paper, check the parameter table and definitions in `Definitions.lean`, then the hypotheses and conclusions in `Theorems.lean`. Successful compilation verifies the intervening algebraic proofs. The geometric and analytic arguments remain in the paper.

## Mathematica

Open [`mathematica/Verification.nb`](mathematica/Verification.nb) in Mathematica and select **Evaluation → Evaluate Notebook**.

The notebook reports `PASS` when each estimate is successfully verified.
