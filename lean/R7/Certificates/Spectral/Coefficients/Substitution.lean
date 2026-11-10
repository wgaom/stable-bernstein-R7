import R7.Spectral.PolynomialCompute
import Mathlib.Algebra.MvPolynomial.Monad
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
open scoped BigOperators
noncomputable def gapSum : PolynomialChart.Poly :=
 MvPolynomial.X 1+(MvPolynomial.X 2+(MvPolynomial.X 3+MvPolynomial.X 4))
noncomputable def subVars (i : Fin 5) : PolynomialChart.Poly :=
 if i=0 then MvPolynomial.X 0*gapSum else MvPolynomial.X i
noncomputable def subHom : PolynomialChart.Poly →ₐ[ℚ] PolynomialChart.Poly :=
 MvPolynomial.aeval subVars

theorem subHom_expr (a : Expr) : subHom a.denote=(substitute a).denote := by
 induction a with
 | rat a => simp [subHom,Expr.denote,substitute]
 | var i => by_cases h : i=0 <;> simp [subHom,Expr.denote,substitute,subVars,h,gapSum]
 | add a b ha hb => simpa [Expr.denote,substitute] using congrArg₂ (·+·) ha hb
 | neg a ha => simpa [Expr.denote,substitute] using congrArg Neg.neg ha
 | mul a b ha hb => simpa [Expr.denote,substitute] using congrArg₂ (·*·) ha hb
 | pow a n ha => simpa [Expr.denote,substitute] using congrArg (·^n) ha

 theorem monomial_finite (e : Exp) (a : ℚ) :
 MvPolynomial.monomial (exponent e) a = MvPolynomial.C a * ∏ i : Fin 5, (MvPolynomial.X i)^e i := by
 rw [MvPolynomial.monomial_eq]
 congr 1
 apply Finset.prod_subset (Finset.subset_univ _)
 intro i hi hn
 simp only [Finsupp.mem_support_iff, not_not] at hn
 simp [hn]

theorem subHom_monomial (e : Exp) (a : ℚ) :
 subHom (MvPolynomial.monomial (exponent e) a) =
 MvPolynomial.monomial (exponent e) a * gapSum^(e 0) := by
 rw [monomial_finite]
 simp only [map_mul,map_prod,map_pow]
 simp [subHom,subVars,Fin.prod_univ_succ,mul_pow]
 ring

theorem subHom_key_group (p : KeyPoly) (k : ℕ) (h : ∀ a∈p, a.exp 0=k) :
 subHom (interpretKey p)=interpretKey p*gapSum^k := by
 induction p with
 | nil => simp [interpretKey]
 | cons a p ih =>
  rw [interpretKey,map_add,subHom_monomial,ih (by intro b hb; exact h b (by simp [hb]))]
  rw [h a (by simp),add_mul]

def gapPower (k : ℕ) : KeyPoly := computeKey (.pow (.add (.var 1) (.add (.var 2) (.add (.var 3) (.var 4)))) k)
@[simp] theorem gapPower_correct (k : ℕ) : interpretKey (gapPower k)=gapSum^k := by
 rw [gapPower,computeKey_correct]
 rfl
end R7.Core.SpectralCoefficient.Expansion
