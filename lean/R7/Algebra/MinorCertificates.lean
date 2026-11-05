import R7.Algebra.Gram
import R7.Algebra.Bivariate

namespace R7.Core.MinorCertificates
open scoped BigOperators
open R7.Core.Univariate
open R7.Core.Bivariate

structure MinorWitness where
  polynomial : Poly
  scale : ℚ
  scale_pos : 0 < scale
  positive : ∀ y : ℝ, 0 ≤ y → 0 < evaluate polynomial y

def coefficient (p : BiPoly) (j : ℕ) : Poly := p[j]?.getD []

def minorPolynomial (p : BiPoly) : ℕ → Poly
  | 0 => [1]
  | 1 => Univariate.scale 2 (coefficient p 0)
  | n+2 => Univariate.add
      (Univariate.mul (Univariate.scale 2 (coefficient p (2*(n+1)))) (minorPolynomial p (n+1)))
      (Univariate.neg (Univariate.mul (Univariate.power (coefficient p (2*n+1)) 2) (minorPolynomial p n)))

theorem evaluate_minorPolynomial (p : BiPoly) (y : ℝ) (n : ℕ) :
    evaluate (minorPolynomial p n) y =
      Gram.delta (fun j => 2*evaluate (coefficient p (2*j)) y)
        (fun j => evaluate (coefficient p (2*j+1)) y) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [minorPolynomial,Gram.delta,evaluate]
  | one => simp [minorPolynomial,Gram.delta]
  | more n ih0 ih1 =>
    simp only [minorPolynomial,evaluate_add,evaluate_mul,evaluate_scale,evaluate_neg,
      evaluate_power,ih0,ih1,Gram.delta]
    push_cast
    ring

theorem eval_eq_sum (p : BiPoly) (x y : ℝ) :
    eval p x y = ∑ j ∈ Finset.range p.length, evaluate (coefficient p j) y*x^j := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [coefficient,List.getElem?_cons_zero,Option.getD_some,pow_zero,mul_one]
    simp only [eval,ih]
    rw [Finset.mul_sum]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [coefficient,pow_succ]
    ring

end R7.Core.MinorCertificates
