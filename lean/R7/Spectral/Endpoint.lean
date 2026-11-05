import R7.Spectral.Coordinates.Representation
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

noncomputable section
namespace R7.Core.Endpoint
open scoped BigOperators

def loss (l : Spectrum) (i : Fin 6) (R : BasisMatrix) : ℝ :=
  inversePair (cMatrix (terminalParameters) l i R)
    (projected R (vVector (terminalParameters) l i))
    (projected R (vVector (terminalParameters) l i)) / 4

def scalar (l : Spectrum) (i : Fin 6) (R : BasisMatrix) (σ ρ : ℝ) : ℝ :=
  σ*(5-2*σ)/10 + (baseL (terminalParameters) l i σ-loss l i R)*ρ
    + ((13:ℝ)/25-(∑ j, (nVector (terminalParameters) l j)^2)/4)*ρ^2

theorem quartic_eq_scalar (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
    (σ y : ℝ) : quartic (terminalParameters) l i R σ y = scalar l i R σ (y^2) := by
  have h11 : ((terminalParameters).m11 : ℝ) = 0 := by
    have h : (terminalParameters).m11 = 0 := by decide
    rw [h]; norm_num
  have h12 : ((terminalParameters).m12 : ℝ) = 0 := by
    have h : (terminalParameters).m12 = 0 := by decide
    rw [h]; norm_num
  have h4 : ((terminalParameters).c4 : ℝ) = 0 := by
    have h : (terminalParameters).c4 = 0 := by decide
    rw [h]; norm_num
  have h8 : ((terminalParameters).c8 : ℝ) = 0 := by
    have h : (terminalParameters).c8 = 0 := by decide
    rw [h]; norm_num
  have h6 : ((terminalParameters).c6 : ℝ) = 13/25 := by
    have h : (terminalParameters).c6 = 13/25 := by rfl
    rw [h]; norm_num
  have h13 : ((terminalParameters).c13 : ℝ) = 0 := by
    have h : (terminalParameters).c13 = 0 := by decide
    rw [h]; norm_num
  unfold quartic quarticCoefficients schurData
  simp only [h11, h12, h4, h8, h6, h13, zero_mul, mul_zero, sub_zero,
    zero_pow (by decide : (2:ℕ) ≠ 0), zero_div, add_zero, sub_self,
    neg_zero]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, pow_one, Nat.reduceAdd]
  unfold scalar loss
  simp only [Fin.sum_univ_succ]
  ring

theorem scalar_bound_of_quartic_bound (l : Spectrum) (i : Fin 6)
    (R : BasisMatrix) (σ ρ a : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ y : ℝ, 0 ≤ y → a+(y^2+y^4)/100000000 ≤
      quartic (terminalParameters) l i R σ y) :
    a+(ρ+ρ^2)/100000000 ≤ scalar l i R σ ρ := by
  have hs := h (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [quartic_eq_scalar, Real.sq_sqrt hρ] at hs
  have h4 : (Real.sqrt ρ)^4 = ρ^2 := by
    rw [show (4:ℕ)=2*2 by decide, pow_mul, Real.sq_sqrt hρ]
  simpa only [Real.sq_sqrt hρ, h4] using hs

end R7.Core.Endpoint
