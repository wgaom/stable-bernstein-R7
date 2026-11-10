import R7.Spectral.Kronecker.Core

/-! Bounded-radix certificates for scaled rational polynomial products and squares. -/
namespace R7.Core.SpectralCoefficient.ScaledPacked
open R7.ComputablePolynomial
open R7.Core.SpectralCoefficient.Kronecker
open Polynomial

/-- Check coefficient scaling and homogeneous degree; packed keys are derived from exponents. -/
def termCheck (D d : ℕ) (a : R7.Core.SpectralCoefficient.Term) : Bool :=
  (scaledNumerator D a.value * (a.value.den : ℤ) == a.value.num * (D : ℤ)) &&
    (totalExp a.exp == d)

def tableCheck (D d : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) : Bool :=
  p.all (termCheck D d)

theorem termCheck_sound (D d : ℕ) (a : R7.Core.SpectralCoefficient.Term)
    (h : termCheck D d a = true) :
    (scaledNumerator D a.value : ℚ) = (D : ℚ) * a.value ∧ totalExp a.exp = d := by
  have hs := Bool.and_eq_true_iff.mp h
  exact ⟨scaledCoefficientCross_sound D a.value _ hs.1, by simpa using hs.2⟩

theorem tableCheck_sound (D d : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (h : tableCheck D d p = true) :
    ∀ a ∈ p, (scaledNumerator D a.value : ℚ) = (D : ℚ) * a.value ∧ totalExp a.exp = d := by
  intro a ha
  exact termCheck_sound D d a ((List.all_eq_true.mp h) a ha)

theorem table_homogeneous (D d : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (h : tableCheck D d p = true) :
    (R7.Core.SpectralCoefficient.interpretKey p).IsHomogeneous d :=
  interpret_homogeneous p d (fun a ha => (tableCheck_sound D d p h a ha).2)

/-- Scale coefficients while retaining keys and exponents. -/
def lifted (D : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Core.SpectralCoefficient.Kronecker.KeyPoly :=
  p.map (fun a => ⟨a.key, a.exp, scaledNumerator D a.value⟩)

theorem lifted_correct_of_forall (D : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (hh : ∀ a ∈ p, (scaledNumerator D a.value : ℚ) = (D : ℚ) * a.value) :
    Kronecker.interpretKey (lifted D p) =
      MvPolynomial.C (D : ℚ) * R7.Core.SpectralCoefficient.interpretKey p := by
  induction p with
  | nil => simp [lifted, Kronecker.interpretKey, R7.Core.SpectralCoefficient.interpretKey]
  | cons a ps ih =>
    have hv := hh a (by simp)
    simp only [lifted, List.map_cons, Kronecker.interpretKey,
      R7.Core.SpectralCoefficient.interpretKey]
    change MvPolynomial.monomial (exponent a.exp) (scaledNumerator D a.value : ℚ) +
      Kronecker.interpretKey (lifted D ps) = _
    rw [hv, ← MvPolynomial.C_mul_monomial,
      ih (fun b hb => hh b (by simp [hb])), mul_add]

theorem lifted_correct (D d : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (h : tableCheck D d p = true) :
    Kronecker.interpretKey (lifted D p) =
      MvPolynomial.C (D : ℚ) * R7.Core.SpectralCoefficient.interpretKey p :=
  lifted_correct_of_forall D p
    (fun a ha => (tableCheck_sound D d p h a ha).1)

namespace Square

def source (base D : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Algebra.Kronecker.Expr :=
  .pow (candidate base (lifted D p)) 2

def result (base D : ℕ) (q : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Algebra.Kronecker.Expr :=
  candidate base (lifted (D^2) q)

/-- Rational square identity from injective bounded-radix evaluation. -/
theorem square (base D d : ℕ) (hb : 1 < base) (hd : 2*d < base) (hD : D ≠ 0)
    (p q : R7.Core.SpectralCoefficient.KeyPoly)
    (hp : tableCheck D d p = true)
    (hq : tableCheck (D^2) (2*d) q = true)
    (hop : ordered (packed base (lifted D p)) = true)
    (hoq : ordered (packed base (lifted (D^2) q)) = true)
    {B : ℤ} (hbound : (source base D p).bound + (result base D q).bound < B)
    (hpoint : (source base D p).evaluateFast B = (result base D q).evaluateFast B) :
    R7.Core.SpectralCoefficient.interpretKey q =
      (R7.Core.SpectralCoefficient.interpretKey p)^2 := by
  have he := R7.Algebra.Kronecker.Expr.identity_of_evaluation
    (source base D p) (result base D q) hbound
    (by simpa only [R7.Algebra.Kronecker.Expr.evaluateFast_correct] using hpoint)
  change (candidate base (lifted D p)).denote ^ 2 =
    (candidate base (lifted (D^2) q)).denote at he
  have hm := congrArg (fun t : Polynomial ℤ => t.map (Int.castRingHom ℚ)) he
  dsimp only at hm
  rw [Polynomial.map_pow, candidate_substitution base _ hop,
    candidate_substitution base _ hoq, lifted_correct D d p hp,
    lifted_correct (D^2) (2*d) q hq, map_mul, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C] at hm
  apply homogeneous_eq_of_substitution_eq base hb _ _ (2*d) hd
    (table_homogeneous _ _ _ hq)
    (by simpa only [Nat.mul_comm] using (table_homogeneous _ _ _ hp).pow 2)
  rw [map_pow]
  have hn : (Polynomial.C (D : ℚ))^2 ≠ 0 := by simp [hD]
  have hc : (Polynomial.C (D : ℚ))^2 *
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)
        (R7.Core.SpectralCoefficient.interpretKey p))^2 =
      (Polynomial.C (D : ℚ))^2 * MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)
        (R7.Core.SpectralCoefficient.interpretKey q) := by
    simpa only [mul_pow, Nat.cast_pow, map_pow] using hm
  exact (mul_left_cancel₀ hn hc).symm

end Square

namespace Product

def source (base Dp Dq : ℕ) (p q : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Algebra.Kronecker.Expr :=
  .mul (candidate base (lifted Dp p)) (candidate base (lifted Dq q))

def result (base Dp Dq : ℕ) (r : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Algebra.Kronecker.Expr := candidate base (lifted (Dp*Dq) r)

/-- Rational product identity from bounded-radix evaluation. -/
theorem multiply (base Dp Dq dp dq : ℕ) (hb : 1<base) (hd : dp+dq<base)
    (hDp : Dp≠0) (hDq : Dq≠0) (p q r : R7.Core.SpectralCoefficient.KeyPoly)
    (hp : tableCheck Dp dp p=true)
    (hq : tableCheck Dq dq q=true)
    (hr : tableCheck (Dp*Dq) (dp+dq) r=true)
    (hop : ordered (packed base (lifted Dp p))=true)
    (hoq : ordered (packed base (lifted Dq q))=true)
    (hor : ordered (packed base (lifted (Dp*Dq) r))=true)
    {B : ℤ} (hbound : (source base Dp Dq p q).bound+(result base Dp Dq r).bound<B)
    (hpoint : (source base Dp Dq p q).evaluateFast B=(result base Dp Dq r).evaluateFast B) :
    R7.Core.SpectralCoefficient.interpretKey r=
      R7.Core.SpectralCoefficient.interpretKey p*R7.Core.SpectralCoefficient.interpretKey q := by
  have he := R7.Algebra.Kronecker.Expr.identity_of_evaluation
    (source base Dp Dq p q) (result base Dp Dq r) hbound
    (by simpa only [R7.Algebra.Kronecker.Expr.evaluateFast_correct] using hpoint)
  change (candidate base (lifted Dp p)).denote*(candidate base (lifted Dq q)).denote=
    (candidate base (lifted (Dp*Dq) r)).denote at he
  have hm := congrArg (fun t : Polynomial ℤ => t.map (Int.castRingHom ℚ)) he
  dsimp only at hm
  rw [Polynomial.map_mul,candidate_substitution base _ hop,
    candidate_substitution base _ hoq,candidate_substitution base _ hor,
    lifted_correct Dp dp p hp,lifted_correct Dq dq q hq,
    lifted_correct (Dp*Dq) (dp+dq) r hr] at hm
  simp only [map_mul,MvPolynomial.eval₂Hom_C] at hm
  apply homogeneous_eq_of_substitution_eq base hb _ _ (dp+dq) hd
    (table_homogeneous _ _ _ hr)
    ((table_homogeneous _ _ _ hp).mul
      (table_homogeneous _ _ _ hq))
  rw [map_mul]
  have hn : Polynomial.C (Dp : ℚ)*Polynomial.C (Dq : ℚ)≠0 := by
    exact mul_ne_zero (by simp [hDp]) (by simp [hDq])
  have hc : (Polynomial.C (Dp : ℚ)*Polynomial.C (Dq : ℚ))*
      ((MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)
        (R7.Core.SpectralCoefficient.interpretKey p))*
       (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)
        (R7.Core.SpectralCoefficient.interpretKey q)))=
      (Polynomial.C (Dp : ℚ)*Polynomial.C (Dq : ℚ))*
        MvPolynomial.eval₂Hom Polynomial.C
          (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)
          (R7.Core.SpectralCoefficient.interpretKey r) := by
    simpa only [Nat.cast_mul,Polynomial.C_mul,mul_assoc,mul_left_comm,mul_comm] using hm
  exact (mul_left_cancel₀ hn hc).symm

end Product

end R7.Core.SpectralCoefficient.ScaledPacked
