import R7.Definitions
import R7.Proofs
import R7.Certificates.Scalar.All

/-! The two algebraic estimates in Appendix A of R7.tex. -/

namespace R7.Paper
open scoped BigOperators

theorem scalar_bound (row : Fin 11) :
 (let p := rows row
  p.m22 > 4*p.c6 ∧ p.c6 > 0 ∧ 0 < p.m11 ∧ p.m11 < 4/5 ∧
  0 ≤ p.m12 ∧ 0 < p.m22*p.m11-p.m12^2 ∧
  p.m12^2 < (p.m22-4*p.c6)/3*(6/5-p.m11)) ∧
 ∀ (side : Fin 2) (q ρ : ℝ),
  0 ≤ q → q ≤ Real.sqrt (5/6 : ℝ) → 0 ≤ ρ →
  (1/10000000 : ℝ)*(1+ρ+ρ^2) ≤ scalarF (rows row) (endpoint row side) q ρ := by
 constructor
 · exact R7.Certificates.Scalar.all_matrix_conditions row
 · intro side q ρ hq hqmax hρ
   exact R7.Certificates.Scalar.endpoint_lower_bound row side q ρ hq hqmax hρ

theorem spectral_bound (l : Fin 6 → ℝ) (i : Fin 6) (σ ρ : ℝ)
 (htrace : ∑ j, l j = 0) (hnorm : ∑ j, (l j)^2 = 1)
 (hσl : 2.4962 ≤ σ) (hσr : σ ≤ 5/2) (hρ : 0 ≤ ρ) :
 (5/2-σ)/3800000+(ρ+ρ^2)/100000000 ≤ spectralF l i σ ρ :=
 R7.Proofs.terminal l i σ ρ htrace hnorm hσl hσr hρ

end R7.Paper
