import R7.Spectral.Slices
import R7.Spectral.PolynomialCompute
import R7.Algebra.Bivariate
import R7.Spectral.CertificateCore

noncomputable section
namespace R7.Core.SpectralGrouped
open scoped BigOperators
open R7.ComputablePolynomial R7.Core.SpectralCoefficient
open R7.Core.SpectralSlices R7.Core.Univariate
open R7.Core.Bivariate
open R7.Core.MinorCertificates
abbrev Groups := List (GapExponent × BiPoly)

def project (p : BiPoly) (j : ℕ) : Univariate.Poly := p.map (fun a => a[j]?.getD 0)

def flattenCoefficients (β : GapExponent) : ℕ → Univariate.Poly → KeyPoly
 | _, [] => []
 | k, a::p =>
   bif a == 0 then flattenCoefficients β (k+1) p
   else
     let e := Fin.cons k β
     ⟨k + 32 * (β 0 + 32 * (β 1 + 32 * (β 2 + 32 * β 3))),e,a⟩ :: flattenCoefficients β (k+1) p

def flattenGrouped (G : Groups) (j : ℕ) : KeyPoly :=
 G.flatMap (fun row => flattenCoefficients row.1 0 (project row.2 j))

@[simp] theorem evaluate_flattenCoefficients (β : GapExponent) (k : ℕ)
    (p : Univariate.Poly) (u : ℝ) (g : Fin 4 → ℝ) :
 MvPolynomial.aeval (point u g) (interpretKey (flattenCoefficients β k p)) =
 gapMonomial β g * u^k * evaluate p u := by
 induction p generalizing k with
 | nil => simp [flattenCoefficients,interpretKey,evaluate]
 | cons a p ih =>
   simp only [flattenCoefficients, cond_eq_ite, beq_iff_eq]
   by_cases ha : a = 0
   · simp only [ha, ite_true]
     rw [ih]
     simp [evaluate, pow_succ, mul_assoc]
   · simp only [ha, ite_false, interpretKey, map_add, MvPolynomial.aeval_monomial,
       Finsupp.prod_pow, Fin.prod_univ_succ]
     simp only [exponent, point, Fin.cons_zero, Fin.cons_succ]
     change (a : ℝ)*(u^k * gapMonomial β g) +
       MvPolynomial.aeval (point u g) (interpretKey (flattenCoefficients β (k+1) p)) = _
     rw [ih]
     simp only [evaluate,pow_succ]
     ring

@[simp] theorem evaluate_flattenGrouped (G : Groups) (j : ℕ) (u : ℝ) (g : Fin 4 → ℝ) :
 MvPolynomial.aeval (point u g) (interpretKey (flattenGrouped G j)) =
 (G.map (fun row => gapMonomial row.1 g * evaluate (project row.2 j) u)).sum := by
 induction G with
 | nil => simp [flattenGrouped,interpretKey]
 | cons row G ih =>
   simp only [flattenGrouped,List.flatMap_cons,interpretKey_append,map_add,
     evaluate_flattenCoefficients,pow_zero,mul_one,List.map_cons,List.sum_cons] at *
   rw [ih]

theorem evaluate_length_three (a : Univariate.Poly) (ha : a.length ≤ 3) (y : ℝ) :
 evaluate a y = ((a[0]?.getD 0 : ℚ) : ℝ)+y*((a[1]?.getD 0 : ℚ) : ℝ)+y^2*((a[2]?.getD 0 : ℚ) : ℝ) := by
 rcases a with _|⟨a,a'⟩
 · simp [evaluate]
 rcases a' with _|⟨b,a'⟩
 · simp [evaluate]
 rcases a' with _|⟨c,a'⟩
 · simp [evaluate]
 have he : a'=[] := by
   cases a' with
   | nil => rfl
   | cons _ _ => simp only [List.length_cons] at ha; omega
 subst a'
 simp [evaluate]
 ring

theorem eval_project_three (p : BiPoly) (hp : ∀ a ∈ p, a.length ≤ 3) (u y : ℝ) :
 eval p u y = evaluate (project p 0) u + y*evaluate (project p 1) u +
 y^2*evaluate (project p 2) u := by
 induction p with
 | nil => simp [eval,project]
 | cons a p ih =>
   rw [eval,ih (fun a ha => hp a (by simp [ha]))]
   simp only [project,List.map_cons,evaluate]
   rw [evaluate_length_three a (hp a (by simp)) y]
   ring

theorem reconstruct_three (G : Groups)
    (hG : ∀ row ∈ G, ∀ a ∈ row.2, a.length ≤ 3)
    (u y : ℝ) (g : Fin 4 → ℝ) :
 MvPolynomial.aeval (point u g) (interpretKey (flattenGrouped G 0)) +
 y*MvPolynomial.aeval (point u g) (interpretKey (flattenGrouped G 1)) +
 y^2*MvPolynomial.aeval (point u g) (interpretKey (flattenGrouped G 2)) =
 (G.map (fun row => gapMonomial row.1 g * eval row.2 u y)).sum := by
 induction G with
 | nil => simp [flattenGrouped,interpretKey]
 | cons row G ih =>
   simp only [evaluate_flattenGrouped,List.map_cons,List.sum_cons]
   have hi := ih (fun row hr => hG row (by simp [hr]))
   simp only [evaluate_flattenGrouped] at hi
   rw [eval_project_three row.2 (hG row (by simp))]
   linear_combination hi

theorem group_sum_nonneg (G : Groups) (u y : ℝ) (g : Fin 4 → ℝ)
    (hg : ∀ j, 0 ≤ g j)
    (hG : ∀ row ∈ G, 0 ≤ eval row.2 u y) :
 0 ≤ (G.map (fun row => gapMonomial row.1 g * eval row.2 u y)).sum := by
 apply List.sum_nonneg
 intro x hx
 obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hx
 exact mul_nonneg (gapMonomial_nonneg row.1 g hg) (hG row hrow)

def flip : BiPoly → BiPoly
 | [] => []
 | a::p => a::Bivariate.neg (flip p)

@[simp] theorem eval_flip (p : BiPoly) (u y : ℝ) : eval (flip p) u y=eval p (-u) y := by
 induction p with
 | nil => rfl
 | cons a p ih => simp only [flip,eval,eval_neg,ih]; ring

structure CertifiedSlice where
 beta : GapExponent
 polynomial : BiPoly
 positive : ∀ (u y : ℝ), 0 ≤ y → 0 < eval polynomial u y

def CertifiedSlice.row (p : CertifiedSlice) : GapExponent × BiPoly := (p.beta,p.polynomial)

def CertifiedSlice.reflected (β : GapExponent) (p : CertifiedSlice) : CertifiedSlice :=
 ⟨β,flip p.polynomial,fun u y hy => by rw [eval_flip]; exact p.positive (-u) y hy⟩

theorem certifiedRows_positive (C : List CertifiedSlice) (row : GapExponent × BiPoly)
    (hrow : row ∈ C.map CertifiedSlice.row) (u y : ℝ) (hy : 0 ≤ y) :
 0 < eval row.2 u y := by
 obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hrow
 exact c.positive u y hy

end R7.Core.SpectralGrouped
