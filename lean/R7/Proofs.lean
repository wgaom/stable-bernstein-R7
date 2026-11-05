import R7.Algebra.QuadraticMinimum
import R7.Spectral.IntervalBounds

noncomputable section
namespace R7.Proofs
open scoped BigOperators
open R7.Paper
open R7.QuadraticMinimum (D evaluatedMinimum)
open R7.Core.Covariance (weights)

def basis : BasisMatrix := fun j a =>
 if j.val = 5 then 1 / Real.sqrt 6
 else (if j.val = a.val then 1 else 0) - (1 + 1 / Real.sqrt 6) / 5

theorem basis_valid : IsTraceFreeOrthonormalBasis basis := by
 have hs : Real.sqrt (6:ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
 have hn : Real.sqrt (6:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
 constructor
 · ext a b
   fin_cases a <;> fin_cases b <;>
    norm_num [basis, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    field_simp <;> nlinarith
 · intro a
   fin_cases a <;> norm_num [basis, Fin.sum_univ_succ] <;> ring

theorem N_eq (l : Spectrum) : N l = nVector (terminalParameters) l := by
 funext j
 unfold terminalParameters
 norm_num [N,c3,c10,c11,s,nVector,moment]
 ring

theorem V_eq (l : Spectrum) (i : Fin 6) : V l i = vVector (terminalParameters) l i := by
 funext j
 unfold terminalParameters
 norm_num [V,c7,c10,c11,c12,s,vVector,moment]

theorem base_eq (l : Spectrum) (i : Fin 6) (σ : ℝ) :
 L l i σ - minimum l i = baseL (terminalParameters) l i σ := by
 unfold terminalParameters
 norm_num [L,N,c3,c5,c6,c7,c10,c11,c12,s,baseL,moment]
 ring

theorem minimum_eq (l : Spectrum) (i : Fin 6) (hl : Normalized l) :
 evaluatedMinimum l i = -Core.Endpoint.loss l i basis := by
 have h := Core.Covariance.inversePair_covariance l i basis hl basis_valid (V l i)
 rw [V_eq] at h
 unfold Core.Endpoint.loss
 rw [h]
 rw [← V_eq]
 have hmean : ∑ j, weights i j*l j = (2/3)*l i := by
  simpa [hl.1] using Core.Covariance.weighted_sum i l
 have hcov : Core.Covariance.covariance i (V l i) l =
   ∑ j, weights i j*V l i j*(l j-l i/4) := by
  unfold Core.Covariance.covariance
  change (∑ j, weights i j*V l i j*l j) - (3/8)*(∑ j, weights i j*V l i j)*(∑ j,weights i j*l j) = _
  rw [hmean]
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  ring
 rw [hcov]
 unfold evaluatedMinimum Core.Covariance.covariance D c5 c6

 have hd : (6.04:ℝ)*(2/3-(l i)^2/2)-0.52 = 138/25-(151/25)*(1/3+(l i)^2/2) := by ring
 rw [hd]
 simp only [pow_two,mul_assoc,Core.Covariance.weights,div_eq_mul_inv,mul_inv_rev]
 norm_num
 ring

theorem spectralF_eq (l : Spectrum) (i : Fin 6) (hl : Normalized l) (σ ρ : ℝ) :
 spectralF l i σ ρ = Core.Endpoint.scalar l i basis σ ρ := by
 have hb := base_eq l i σ
 have hm := minimum_eq l i hl
 have hmin := QuadraticMinimum.minimum_eq l i hl.1 hl.2
 unfold spectralF Core.Endpoint.scalar Q
 rw [N_eq]
 unfold c6
 rw [show L l i σ = baseL (terminalParameters) l i σ - Core.Endpoint.loss l i basis by linarith]
 norm_num

theorem terminal (l : Fin 6 → ℝ) (i : Fin 6) (σ ρ : ℝ)
 (htrace : ∑ j, l j = 0) (hnorm : ∑ j, (l j)^2 = 1)
 (hσl : 2.4962 ≤ σ) (hσr : σ ≤ 5/2) (hρ : 0 ≤ ρ) :
 (5/2-σ)/3800000+(ρ+ρ^2)/100000000 ≤ Paper.spectralF l i σ ρ := by
 rw [spectralF_eq l i ⟨htrace,hnorm⟩]
 exact Core.SpectralCertificateTheorem.scalar_interval_bound σ (by norm_num at *; assumption)
  hσr l i basis ⟨htrace,hnorm⟩ basis_valid ρ hρ
end R7.Proofs
