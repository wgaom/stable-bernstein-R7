import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace R7.Core.RankOne
open scoped Matrix
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inverse_update (H K : Matrix n n ℝ) (u : n → ℝ) (a d : ℝ)
    (hHK : H*K=1) (hK : K.transpose=K) (ha : a ≠ 0)
    (hδ : a-d*(u ⬝ᵥ (K*ᵥu)) ≠ 0) :
    (a • H-d • vecMulVec u u)⁻¹ =
      a⁻¹ • K + (d/(a*(a-d*(u ⬝ᵥ (K*ᵥu))))) • vecMulVec (K*ᵥu) (K*ᵥu) := by
  apply Matrix.inv_eq_right_inv
  have hHu : H *ᵥ (K*ᵥu) = u := by
    rw [Matrix.mulVec_mulVec, hHK, Matrix.one_mulVec]
  have huK : u ᵥ* K = K*ᵥu := by
    have h := Matrix.mulVec_transpose K u
    rw [hK] at h
    exact h.symm
  have hRank : vecMulVec u u *ᵥ (K*ᵥu) = (u ⬝ᵥ (K*ᵥu)) • u := by
    rw [Matrix.vecMulVec_mulVec]
    ext j
    simp [smul_eq_mul, mul_comm]
  simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hHK, mul_vecMulVec, hHu, vecMulVec_mul, huK,
    Matrix.smul_mulVec, hRank, Matrix.smul_vecMulVec]
  let t : ℝ := u ⬝ᵥ (K*ᵥu)
  let r : ℝ := d/(a*(a-d*t))
  let B := vecMulVec u (K*ᵥu)
  have hc : a*r-d*a⁻¹-d*r*t = 0 := by
    dsimp [r,t]
    field_simp [ha,hδ]
    ring
  have haa : a⁻¹*a=1 := inv_mul_cancel₀ ha
  rw [haa, one_smul]
  calc
    _ = 1 + (a*r-d*a⁻¹-d*r*t) • B := by dsimp [r,t,B]; module
    _ = 1 := by rw [hc,zero_smul,add_zero]

theorem pairing_update (H K : Matrix n n ℝ) (u x : n → ℝ) (a d : ℝ)
    (hHK : H*K=1) (hK : K.transpose=K) (ha : a ≠ 0)
    (hδ : a-d*(u ⬝ᵥ (K*ᵥu)) ≠ 0) :
    x ⬝ᵥ ((a • H-d • vecMulVec u u)⁻¹*ᵥx) =
      (x ⬝ᵥ (K*ᵥx))/a + d*(x ⬝ᵥ (K*ᵥu))^2/(a*(a-d*(u ⬝ᵥ (K*ᵥu)))) := by
  rw [inverse_update H K u a d hHK hK ha hδ]
  rw [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,
    Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,op_smul_eq_smul,dotProduct_smul,
    dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm (K*ᵥu) x]
  ring

end R7.Core.RankOne
