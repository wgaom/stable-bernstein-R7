import R7.Spectral.Kronecker.ReducedPointCertificate
import R7.Certificates.Spectral.Coefficients.Substitution

namespace R7.Core.SpectralCoefficient.Kronecker.Reduced
open R7.ComputablePolynomial Polynomial

/-- The gap sum after three-digit substitution. The homogenizing gap is one. -/
def gapExpr (base : ℕ) : R7.Algebra.Kronecker.Expr :=
  .add (.variable 1) (.add (.variable base) (.add (.variable (base^2)) (.constant 1)))

theorem gapExpr_correct (base : ℕ) :
    (gapExpr base).denote.map (Int.castRingHom ℚ)=apply base Expansion.gapSum := by
  simp [gapExpr,R7.Algebra.Kronecker.Expr.denote,apply,Expansion.gapSum,weight]

theorem fixedU_X (i : Fin 5) (hi : i≠0) : FixedU (MvPolynomial.X i : Poly) 0 := by
  apply FixedU.monomial
  simp [Ne.symm hi]

theorem fixedU_gapSum : FixedU Expansion.gapSum 0 := by
  apply FixedU.add (fixedU_X 1 (by decide))
  exact (fixedU_X 2 (by decide)).add ((fixedU_X 3 (by decide)).add (fixedU_X 4 (by decide)))

theorem FixedU.pow_zero {p : Poly} (h : FixedU p 0) (n : ℕ) : FixedU (p^n) 0 := by
  induction n with
  | zero =>
    simpa using FixedU.monomial (0 : Fin 5 →₀ ℕ) 1 0 rfl
  | succ n ih => simpa only [pow_succ,Nat.add_zero] using ih.mul h

theorem gapSum_homogeneous : Expansion.gapSum.IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_X _ 1).add
    ((MvPolynomial.isHomogeneous_X _ 2).add
      ((MvPolynomial.isHomogeneous_X _ 3).add (MvPolynomial.isHomogeneous_X _ 4)))

theorem gap_point_identity (base j : ℕ) (p r : R7.Core.SpectralCoefficient.KeyPoly)
    {B : ℤ}
    (hbound : R7.Algebra.Kronecker.mass (raw base p)*4^j+
      R7.Algebra.Kronecker.mass (raw base r)<B)
    (hpoint : (candidate base p).evaluateFast B*
      R7.Algebra.KernelPower.fastPow ((gapExpr base).evaluateFast B) j=
      (candidate base r).evaluateFast B) :
    R7.Algebra.Kronecker.polynomial (raw base p)*(gapExpr base).denote^j=
      R7.Algebra.Kronecker.polynomial (raw base r) := by
  have hB : 0<B := lt_of_le_of_lt
    (add_nonneg (mul_nonneg (R7.Algebra.Kronecker.mass_nonneg _) (by positivity))
      (R7.Algebra.Kronecker.mass_nonneg _)) hbound
  apply R7.Algebra.Kronecker.eq_of_eval_eq hB
  · intro n
    have ha := R7.Algebra.Kronecker.coefficient_abs_le_mass
      (R7.Algebra.Kronecker.times (raw base p)
        (R7.Algebra.Kronecker.Expr.pow (gapExpr base) j).terms) n
    rw [R7.Algebra.Kronecker.polynomial_times, R7.Algebra.Kronecker.mass_times,
      R7.Algebra.Kronecker.Expr.polynomial_terms,R7.Algebra.Kronecker.Expr.mass_terms] at ha
    change |(R7.Algebra.Kronecker.polynomial (raw base p)*(gapExpr base).denote^j).coeff n| ≤
      R7.Algebra.Kronecker.mass (raw base p)*(gapExpr base).bound^j at ha
    have hgb : (gapExpr base).bound=4 := by simp [gapExpr,R7.Algebra.Kronecker.Expr.bound]
    rw [hgb] at ha
    exact lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add ha
      (R7.Algebra.Kronecker.coefficient_abs_le_mass (raw base r) n))) hbound
  · rw [← candidate_raw base p (packed_ordered base p),
      ← candidate_raw base r (packed_ordered base r)]
    simpa only [Polynomial.eval_mul,Polynomial.eval_pow,
      R7.Algebra.Kronecker.Expr.evaluate_correct,
      ← R7.Algebra.Kronecker.Expr.evaluateFast_correct,
      R7.Algebra.KernelPower.fastPow_eq_pow] using hpoint

/-- Gap-power certificate on a fixed-u slice. -/
theorem multiply_gap (base j d : ℕ) (p r : R7.Core.SpectralCoefficient.KeyPoly)
    (hb : 1<base) (hd : d<base)
    (hp : tableCheck p j d=true) (hr : tableCheck r j (d+j)=true)
    {B : ℤ}
    (hbound : R7.Algebra.Kronecker.mass (raw base p)*4^j+
      R7.Algebra.Kronecker.mass (raw base r)<B)
    (hpoint : (candidate base p).evaluateFast B*
      R7.Algebra.KernelPower.fastPow ((gapExpr base).evaluateFast B) j=
      (candidate base r).evaluateFast B) :
    R7.Core.SpectralCoefficient.interpretKey p * Expansion.gapSum^j =
      R7.Core.SpectralCoefficient.interpretKey r := by
  have hi := gap_point_identity base j p r hbound hpoint
  have hm := congrArg (fun t : Polynomial ℤ => t.map (Int.castRingHom ℚ)) hi
  dsimp only at hm
  rw [Polynomial.map_mul,Polynomial.map_pow,
    raw_correct base p (fun a ha => (tableCheck_sound p j d hp a ha).1),
    raw_correct base r (fun a ha => (tableCheck_sound r j (d+j) hr a ha).1),gapExpr_correct] at hm
  have ph := interpret_homogeneous p d (fun a ha => (tableCheck_sound p j d hp a ha).2.2)
  have rh := interpret_homogeneous r (d+j) (fun a ha => (tableCheck_sound r j (d+j) hr a ha).2.2)
  have pu := fixedU_table p j (fun a ha => (tableCheck_sound p j d hp a ha).2.1)
  have ru := fixedU_table r j (fun a ha => (tableCheck_sound r j (d+j) hr a ha).2.1)
  apply eq_of_apply_eq base j d hb hd _ _
    (by simpa only [Nat.add_comm,one_mul] using ph.mul (gapSum_homogeneous.pow j))
    (by simpa only [Nat.add_comm] using rh)
    (by simpa only [Nat.add_zero] using pu.mul (fixedU_gapSum.pow_zero j)) ru
  simpa only [map_mul,map_pow] using hm

end R7.Core.SpectralCoefficient.Kronecker.Reduced
