import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace R7.Core

theorem six_five_projector (R : Matrix (Fin 6) (Fin 5) ℝ)
    (horth : R.transpose * R = 1)
    (hzero : ∀ j, ∑ i, R i j = 0) :
    R * R.transpose = 1 - (1/6 : ℝ) • Matrix.of (fun _ _ => 1) := by
  let c : ℝ := 1 / Real.sqrt 6
  have hs : (Real.sqrt (6 : ℝ))^2 = 6 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (6 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc : c*c = 1/6 := by
    dsimp [c]
    field_simp
    nlinarith [hs]
  let Q : Matrix (Fin 6) (Fin 6) ℝ := fun i j =>
    Fin.cases c (fun k : Fin 5 => R i k) j
  have hQ : Q.transpose * Q = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [Q, Matrix.mul_apply, Matrix.transpose_apply, hc]
      · have hne : (0 : Fin 6) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
        simp [Q, Matrix.mul_apply, Matrix.transpose_apply, ← Finset.mul_sum, hzero, hne]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [Q, Matrix.mul_apply, Matrix.transpose_apply, ← Finset.sum_mul, hzero]
      · simpa [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
          congrArg (fun A : Matrix (Fin 5) (Fin 5) ℝ => A i j) horth
  have hQQ : Q * Q.transpose = 1 := mul_eq_one_comm.2 hQ
  ext i j
  have hentry := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A i j) hQQ
  change (∑ k : Fin 6, Q i k*Q j k) = (1 : Matrix (Fin 6) (Fin 6) ℝ) i j at hentry
  rw [Fin.sum_univ_succ] at hentry
  simp only [Q, Fin.cases_zero, Fin.cases_succ] at hentry
  rw [hc] at hentry
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one,
    Matrix.mul_apply, Matrix.transpose_apply]
  linarith [hentry]

end R7.Core
