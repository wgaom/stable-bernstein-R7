import Mathlib.Data.Rat.Defs

/-! Scalar parameters; the rows of Table A.1 are in R7/Definitions.lean. -/

namespace R7.Core

structure Parameters where
  sigmaL : ℚ
  sigmaR : ℚ
  c3 : ℚ
  c6 : ℚ
  m22 : ℚ
  c7 : ℚ
  m11 : ℚ
  c4 : ℚ
  m12 : ℚ
  c8 : ℚ
  deriving DecidableEq

def MatrixSigns (p : Parameters) : Prop :=
  p.m22 > 4*p.c6 ∧ p.c6 > 0 ∧ 0 < p.m11 ∧ p.m11 < 4/5 ∧
  0 ≤ p.m12 ∧ 0 < p.m22*p.m11-p.m12^2 ∧
  p.m12^2 < (p.m22-4*p.c6)/3*(6/5-p.m11)

end R7.Core
