import R7.Algebra.IntegerExpression
import R7.Algebra.ComputablePolynomial
import Mathlib.Tactic.Ring

/-! LCM denominator clearing for the existing rational expression AST. -/
namespace R7.Algebra.Kronecker
open Polynomial
/-- Clearing denominators constructs an integer expression, without expanding
any polynomial. Denominators are positive natural numbers by construction. -/
structure Cleared where
  numerator : Expr
  denominator : ℕ
  positive : 0 < denominator

def clear (weight : Fin 5 → ℕ) : ComputablePolynomial.Expr → Cleared
  | .rat q => ⟨.constant q.num,q.den,q.den_pos⟩
  | .var i => ⟨.variable (weight i),1,by decide⟩
  | .add a b =>
      let ca := clear weight a
      let cb := clear weight b
      ⟨.add (.mul (.constant cb.denominator) ca.numerator)
        (.mul (.constant ca.denominator) cb.numerator),
        ca.denominator*cb.denominator,Nat.mul_pos ca.positive cb.positive⟩
  | .neg a => let ca := clear weight a
      ⟨.neg ca.numerator,ca.denominator,ca.positive⟩
  | .mul a b =>
      let ca := clear weight a
      let cb := clear weight b
      ⟨.mul ca.numerator cb.numerator,ca.denominator*cb.denominator,
        Nat.mul_pos ca.positive cb.positive⟩
  | .pow a n => let ca := clear weight a
      ⟨.pow ca.numerator n,ca.denominator^n,pow_pos ca.positive n⟩

/-- Structural coefficient bound for the denominator-cleared expression. -/
theorem cleared_coefficient_bound (weight : Fin 5 → ℕ)
    (e : ComputablePolynomial.Expr) (n : ℕ) :
    |(clear weight e).numerator.denote.coeff n| ≤ (clear weight e).numerator.bound :=
  (clear weight e).numerator.coefficient_bound n

noncomputable def rationalExpression (weight : Fin 5 → ℕ) :
    ComputablePolynomial.Expr → Polynomial ℚ
  | .rat q => Polynomial.C q
  | .var i => Polynomial.X^(weight i)
  | .add a b => rationalExpression weight a+rationalExpression weight b
  | .neg a => -rationalExpression weight a
  | .mul a b => rationalExpression weight a*rationalExpression weight b
  | .pow a n => rationalExpression weight a^n

/-- Denominator clearing preserves the rational polynomial. -/
theorem clear_correct (weight : Fin 5 → ℕ) (e : ComputablePolynomial.Expr) :
    (clear weight e).numerator.denote.map (Int.castRingHom ℚ) =
      Polynomial.C ((clear weight e).denominator : ℚ) * rationalExpression weight e := by
  induction e with
  | rat q =>
      simp only [clear,Expr.denote,Polynomial.map_C,rationalExpression]
      rw [← Polynomial.C_mul]
      congr 1
      have hh := Rat.num_div_den q
      have hn : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos)
      apply (div_eq_iff hn).mp at hh
      exact hh.trans (mul_comm q (q.den : ℚ))
  | var i => simp [clear,Expr.denote,rationalExpression]
  | add a b ha hb =>
      simp only [clear,Expr.denote,rationalExpression,Polynomial.map_add,Polynomial.map_mul,
        map_natCast,Polynomial.map_natCast,ha,hb,Nat.cast_mul,Polynomial.C_mul]
      ring
  | neg a ha => simp [clear,Expr.denote,rationalExpression,ha]
  | mul a b ha hb =>
      simp only [clear,Expr.denote,rationalExpression,Polynomial.map_mul,ha,hb,
        Nat.cast_mul,Polynomial.C_mul]
      ring
  | pow a n ha =>
      simp only [clear,Expr.denote,rationalExpression,Polynomial.map_pow,ha,
        Nat.cast_pow,map_pow,mul_pow]

/-- The polynomial being bounded is exactly the Kronecker substitution of the
existing, paper-bound AST semantics. -/
theorem rationalExpression_correct (weight : Fin 5 → ℕ) (e : ComputablePolynomial.Expr) :
    rationalExpression weight e =
      MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.X ^ weight i) e.denote := by
  induction e <;> simp_all [rationalExpression,ComputablePolynomial.Expr.denote]

/-- Rational addition with an LCM denominator. -/
def clearLCM (weight : Fin 5 → ℕ) : ComputablePolynomial.Expr → Cleared
  | .rat q => ⟨.constant q.num,q.den,q.den_pos⟩
  | .var i => ⟨.variable (weight i),1,by decide⟩
  | .add a b =>
      let ca := clearLCM weight a
      let cb := clearLCM weight b
      let D := Nat.lcm ca.denominator cb.denominator
      ⟨.add (.mul (.constant ((D/ca.denominator : ℕ) : ℤ)) ca.numerator)
        (.mul (.constant ((D/cb.denominator : ℕ) : ℤ)) cb.numerator),D,
        Nat.lcm_pos ca.positive cb.positive⟩
  | .neg a => let ca := clearLCM weight a
      ⟨.neg ca.numerator,ca.denominator,ca.positive⟩
  | .mul a b =>
      let ca := clearLCM weight a
      let cb := clearLCM weight b
      ⟨.mul ca.numerator cb.numerator,ca.denominator*cb.denominator,
        Nat.mul_pos ca.positive cb.positive⟩
  | .pow a n => let ca := clearLCM weight a
      ⟨.pow ca.numerator n,ca.denominator^n,pow_pos ca.positive n⟩

theorem clearLCM_correct (weight : Fin 5 → ℕ) (e : ComputablePolynomial.Expr) :
    (clearLCM weight e).numerator.denote.map (Int.castRingHom ℚ) =
      Polynomial.C ((clearLCM weight e).denominator : ℚ) * rationalExpression weight e := by
  induction e with
  | rat q =>
      simpa only [clearLCM,clear] using clear_correct weight (.rat q)
  | var i => simp [clearLCM,Expr.denote,rationalExpression]
  | add a b ha hb =>
      have hda : (Nat.lcm (clearLCM weight a).denominator (clearLCM weight b).denominator /
          (clearLCM weight a).denominator) * (clearLCM weight a).denominator =
          Nat.lcm (clearLCM weight a).denominator (clearLCM weight b).denominator :=
        Nat.div_mul_cancel (Nat.dvd_lcm_left _ _)
      have hdb : (Nat.lcm (clearLCM weight a).denominator (clearLCM weight b).denominator /
          (clearLCM weight b).denominator) * (clearLCM weight b).denominator =
          Nat.lcm (clearLCM weight a).denominator (clearLCM weight b).denominator :=
        Nat.div_mul_cancel (Nat.dvd_lcm_right _ _)
      have hqa := congrArg (fun n : ℕ => (n : Polynomial ℚ)) hda
      have hqb := congrArg (fun n : ℕ => (n : Polynomial ℚ)) hdb
      simp only [Nat.cast_mul] at hqa hqb
      simp only [clearLCM,Expr.denote,rationalExpression,Polynomial.map_add,Polynomial.map_mul,
        map_natCast,Polynomial.map_natCast,ha,hb]
      rw [← mul_assoc, hqa, ← mul_assoc, hqb, mul_add]
  | neg a ha => simp [clearLCM,Expr.denote,rationalExpression,ha]
  | mul a b ha hb =>
      simp only [clearLCM,Expr.denote,rationalExpression,Polynomial.map_mul,ha,hb,
        Nat.cast_mul,Polynomial.C_mul]
      ring
  | pow a n ha =>
      simp only [clearLCM,Expr.denote,rationalExpression,Polynomial.map_pow,ha,
        Nat.cast_pow,map_pow,mul_pow]

/-- Identity with a scaled polynomial from bounded evaluation. -/
theorem clearLCM_identity_of_evaluation (weight : Fin 5 → ℕ)
    (source : ComputablePolynomial.Expr) (candidate : Expr) (k : ℕ) {B : ℤ}
    (hb : (Expr.mul (.constant k) (clearLCM weight source).numerator).bound +
      (Expr.mul (.constant (clearLCM weight source).denominator) candidate).bound < B)
    (he : (Expr.mul (.constant k) (clearLCM weight source).numerator).evaluate B =
      (Expr.mul (.constant (clearLCM weight source).denominator) candidate).evaluate B) :
    Polynomial.C (k : ℚ) * rationalExpression weight source =
      candidate.denote.map (Int.castRingHom ℚ) := by
  have hh := Expr.identity_of_evaluation _ _ hb he
  have hm := congrArg (fun p : Polynomial ℤ => p.map (Int.castRingHom ℚ)) hh
  simp only [Expr.denote,Polynomial.map_mul,map_natCast,
    Polynomial.map_natCast,clearLCM_correct] at hm
  have hd : (↑(clearLCM weight source).denominator : Polynomial ℚ) ≠ 0 := by
    simpa using (Nat.ne_of_gt (clearLCM weight source).positive)
  apply mul_left_cancel₀ hd
  calc
    _ = (↑k : Polynomial ℚ) * (↑(clearLCM weight source).denominator * rationalExpression weight source) := by simp only [map_natCast]; ring
    _ = _ := hm

end R7.Algebra.Kronecker
