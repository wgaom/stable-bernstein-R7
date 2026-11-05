import R7.Definitions
import R7.Scalar.Expression

namespace R7.ScalarBridge
open R7.Paper

theorem beta_sq (p : Parameters) (y : ℝ) (hy : 0 ≤ y) :
    beta p (y^2) = R7.Core.beta p y := by
  unfold beta R7.Core.beta Core.j
  rw [Real.sqrt_sq hy]
  congr 1
  ring

theorem m11tilde_sq (p : Parameters) (y : ℝ) (hy : 0 ≤ y) :
    m11tilde p (y^2) = R7.Core.m11tilde p y := by
  simp only [m11tilde, R7.Core.m11tilde, beta_sq p y hy]

theorem m12tilde_sq (p : Parameters) (y : ℝ) (hy : 0 ≤ y) :
    m12tilde p (y^2) = R7.Core.m12tilde p y := by
  simp only [m12tilde, R7.Core.m12tilde, beta_sq p y hy, Real.sqrt_sq hy]

theorem alpha_sq (p : Parameters) (q y : ℝ) (hy : 0 ≤ y) :
    alpha p q (y^2) = Core.alphaSq p (q^2) y := by
  simp only [alpha, Core.alphaSq, Core.spectralFactor, beta_sq p y hy]

theorem eta_sq (p : Parameters) (q y : ℝ) (hy : 0 ≤ y) :
    eta p q (y^2) = Core.etaSq p (q^2) y := by
  rw [eta, m11tilde_sq p y hy, m12tilde_sq p y hy, alpha_sq p q y hy]
  unfold Core.etaSq
  rw [Core.alphaInvSq_eq_inv_alphaSq p (q^2) y (by unfold Core.spectralFactor; positivity)]
  ring

theorem B0_sq (p : Parameters) (σ u y : ℝ) (hy : 0 ≤ y) :
    B0 p σ u (y^2) = R7.Core.B0 p σ u y := by
  simp only [B0, R7.Core.B0, beta_sq p y hy, Real.sqrt_sq hy]
  ring

theorem B1_sq (p : Parameters) (σ y : ℝ) (hy : 0 ≤ y) :
    B1 p σ (y^2) = R7.Core.B1 p σ y := by
  simp only [B1, R7.Core.B1, beta_sq p y hy, Real.sqrt_sq hy]

theorem B2_sq (p : Parameters) (σ y : ℝ) (hy : 0 ≤ y) :
    B2 p σ (y^2) = R7.Core.B2 p σ y := by
  simp only [B2, R7.Core.B2, beta_sq p y hy, Real.sqrt_sq hy]

theorem scalarF_sq (p : Parameters) (σ q y : ℝ) (hy : 0 ≤ y) :
    scalarF p σ q (y^2) = R7.Core.scalarF p σ q y := by
  unfold Paper.scalarF R7.Core.scalarF Core.scalarCore
  rw [B0_sq p σ (q^2) y hy, B1_sq p σ y hy, B2_sq p σ y hy,
    m12tilde_sq p y hy, alpha_sq p q y hy, eta_sq p q y hy]
  rw [Core.alphaInvSq_eq_inv_alphaSq p (q^2) y (by unfold Core.spectralFactor; positivity)]
  unfold Paper.Lambda
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem scalarF_eq (p : Parameters) (σ q ρ : ℝ) (hρ : 0 ≤ ρ) :
    scalarF p σ q ρ = R7.Core.scalarF p σ q (Real.sqrt ρ) := by
  simpa only [Real.sq_sqrt hρ] using
    scalarF_sq p σ q (Real.sqrt ρ) (Real.sqrt_nonneg ρ)

end R7.ScalarBridge
