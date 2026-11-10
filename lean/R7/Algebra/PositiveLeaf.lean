import R7.Algebra.Univariate
import Mathlib.Algebra.Polynomial.Roots

namespace R7.Core.Univariate.PositiveLeaf
open R7.Core.Univariate
open scoped BigOperators

noncomputable def denote : Poly → Polynomial ℝ
  | [] => 0
  | a :: p => Polynomial.C (a : ℝ) + Polynomial.X * denote p

@[simp] theorem eval_denote (p : Poly) (x : ℝ) :
    (denote p).eval x = evaluate p x := by
  induction p with
  | nil => simp [denote, evaluate]
  | cons a p ih => simp [denote, evaluate, ih]

@[simp] theorem denote_add (p q : Poly) : denote (add p q) = denote p + denote q := by
  induction p generalizing q with
  | nil => simp [add, denote]
  | cons a p ih =>
    cases q with
    | nil => simp [add, denote]
    | cons b q => simp only [add, denote, Rat.cast_add, map_add, ih]; ring

@[simp] theorem denote_neg (p : Poly) : denote (neg p) = -denote p := by
  induction p with
  | nil => simp [neg, denote]
  | cons a p ih => simp only [neg, List.map_cons, denote, Rat.cast_neg, map_neg] at *; rw [ih]; ring

theorem all_zero_of_denote_zero (p : Poly) (h : denote p = 0) : p.all (· == 0) = true := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have haR : (a : ℝ) = 0 := by
      simpa [denote] using congrArg (fun q : Polynomial ℝ => q.coeff 0) h
    have ha : a = 0 := by exact_mod_cast haR
    have hp : denote p = 0 := by
      have hmul : Polynomial.X * denote p = 0 := by simpa [denote, ha] using h
      exact (mul_eq_zero.mp hmul).resolve_left Polynomial.X_ne_zero
    simp [ha, ih hp]

theorem equal_of_evaluate_eq (p q : Poly)
    (h : ∀ x : ℝ, evaluate p x = evaluate q x) : equal p q = true := by
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  have hd : denote p = denote q := Polynomial.funext (by simpa only [eval_denote] using h)
  apply all_zero_of_denote_zero
  simp [hd]

theorem evaluate_compactify_ofFn (n : ℕ) (c : Fin (n+1) → ℚ) (x : ℝ) :
    evaluate (compactify (List.ofFn c) n) x =
      ∑ j, (c j : ℝ) * x^j.val * (1-x)^(n-j.val) := by
  induction n with
  | zero => simp [compactify, evaluate]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [compactify, evaluate_add, evaluate_scale, evaluate_power,
      evaluate_mul, evaluate_cons, evaluate_nil, Rat.cast_zero, Rat.cast_one,
      mul_zero, add_zero, zero_add, Rat.cast_neg]
    rw [ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Nat.sub_zero, Fin.val_succ,
      Nat.add_sub_add_right]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring

theorem compactify_equal_compactPolynomial (n : ℕ) (c : Fin (n+1) → ℚ) :
    equal (compactify (List.ofFn c) n) (compactPolynomial n 0 1 c) = true := by
  apply equal_of_evaluate_eq
  intro x
  rw [evaluate_compactify_ofFn, evaluate_compactPolynomial]
  simp

/-- Acceptance of a positive-coefficient leaf. -/
theorem checkCompactified_ofFn_leaf (n : ℕ) (c : Fin (n+1) → ℚ)
    (hc : ∀ j, 0 < c j) :
    checkCompactified (List.ofFn c) n (.leaf n c) = true := by
  simp only [checkCompactified, List.length_ofFn, le_refl, decide_true, checkCompact,
    zero_lt_one, hc, implies_true, and_self, Bool.true_and,
    compactify_equal_compactPolynomial]

theorem checkCompactified_leaf_of_coefficients (p : Poly) (n : ℕ)
    (c : Fin (n+1) → ℚ) (hp : p = List.ofFn c) (hc : ∀ j, 0 < c j) :
    checkCompactified p n (.leaf n c) = true := by
  rw [hp]
  exact checkCompactified_ofFn_leaf n c hc

end R7.Core.Univariate.PositiveLeaf
