# Stable Bernstein in R⁷: algebraic verification

Mathematica code for the finite algebraic checks in Propositions 8.1 and 10.1 of the accompanying paper on the stable Bernstein problem for six-dimensional minimal hypersurfaces in **R⁷**.

**Paper:** [Manuscript link](https://example.com/manuscript) *(to be updated)*.

## Notebook

Open [`R7Verification.nb`](R7Verification.nb) in Mathematica, start a fresh kernel, and evaluate the notebook from top to bottom. It contains all required parameters and formulas; no companion files are needed to run the notebook.

| Section | Contents |
| --- | --- |
| 1. Parameters and positivity tools | Parameter tables, Sturm sequences, Gram matrices, and leading principal minors. |
| 2. Proposition 8.1: bridge estimates | Polynomial construction, an expanded example at the first left endpoint, and verification of all fifteen bridge intervals. |
| 3. Proposition 10.1: spectral estimates | Homogeneous polynomial construction, gap expansion and reflection symmetry, an expanded example at the entry exponent, and verification at the entry and critical exponents, including boundary cases. |
| 4. Summary | Results and checks that all required cases are included. |

The examples display coefficient polynomials and leading principal minors before applying the positivity tests. The final summary reports `PASS` for each proposition when all its algebraic checks succeed. A failed check stops evaluation.

## Verification scope

- **Proposition 8.1:** parameter feasibility, interval coverage over `[2.46, 2.4962]`, agreement of polynomial reconstructions, and **120 Sturm tests** for the leading principal minors of 30 endpoint matrices.
- **Proposition 10.1:** parameter conditions, homogeneous polynomial reconstruction, reflection symmetry, and complete coverage of the coefficient slices. At exponent `2.4962`, the code performs **1617 Sturm tests** for 231 matrices. At exponent `5/2`, it checks **2042 principal-minor signs** for 231 linear-term matrices and 85 quadratic-term matrices. Zero-gap boundary checks are included separately.

The verification uses exact integer and rational arithmetic. Parameter tables display terminating decimals without trailing zeros and other values as reduced fractions. Sturm's theorem certifies polynomial positivity on the nonnegative half-line; these tests do not rely on sampling numerical points.

The notebook verifies the finite algebraic conditions used in the two propositions. The arguments extending endpoint estimates to the intervening exponents, together with the geometric and analytic parts of the proof, are given in the paper.

