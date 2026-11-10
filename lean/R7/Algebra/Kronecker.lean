import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Lean.Elab.Tactic.Omega

/-! Deterministic one-point identity certificates, using signed radix digits. -/
namespace R7.Algebra.Kronecker
open Polynomial

/-- Coefficients strictly smaller in absolute value than the positive radix
make a zero evaluation a deterministic polynomial identity certificate. -/
theorem eq_zero_of_eval_eq_zero {B : ℤ} (hB : 0 < B) (p : Polynomial ℤ)
    (hc : ∀ n, |p.coeff n| < B) (he : p.eval B = 0) : p = 0 := by
  generalize hn : p.natDegree = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    have hconst : p.coeff 0 = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd _ (hc 0)
      refine ⟨-p.divX.eval B, ?_⟩
      have hh := congrArg (fun q : Polynomial ℤ => q.eval B) (divX_mul_X_add p)
      simp only [eval_add, eval_mul, eval_X, eval_C, he] at hh
      simpa only [mul_neg, neg_mul, mul_comm B] using (eq_neg_of_add_eq_zero_right hh)
    have ht : p.divX.eval B = 0 := by
      have hh := congrArg (fun q : Polynomial ℤ => q.eval B) (divX_mul_X_add p)
      simp only [eval_add, eval_mul, eval_X, eval_C, he, hconst, add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hB)
    by_cases hn0 : n = 0
    · have hp := eq_C_of_natDegree_eq_zero (hn.trans hn0)
      simpa [hconst] using hp
    · have hdeg : p.divX.natDegree < n := by
        rw [natDegree_divX_eq_natDegree_tsub_one, hn]
        omega
      have hz := ih p.divX.natDegree hdeg p.divX
        (fun k => by simpa only [coeff_divX] using hc (k+1)) ht rfl
      simpa [hz, hconst] using (divX_mul_X_add p).symm

/-- One exact evaluation proves equality, provided the coefficient bound is
verified for the difference. -/
theorem eq_of_eval_eq {B : ℤ} (hB : 0 < B) (p q : Polynomial ℤ)
    (hc : ∀ n, |p.coeff n - q.coeff n| < B)
    (he : p.eval B = q.eval B) : p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_eq_zero hB
  · simpa only [coeff_sub] using hc
  · simpa only [eval_sub, sub_eq_zero] using he

end R7.Algebra.Kronecker
