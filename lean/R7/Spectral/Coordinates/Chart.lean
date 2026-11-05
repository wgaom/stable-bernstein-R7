import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace R7.SpectralChart

def kappa (s : ℝ) (g : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![5*s, -s-4*g 0-3*g 1-2*g 2-g 3,
    -s+g 0-3*g 1-2*g 2-g 3,
    -s+g 0+2*g 1-2*g 2-g 3,
    -s+g 0+2*g 1+3*g 2-g 3,
    -s+g 0+2*g 1+3*g 2+4*g 3]

theorem kappa_trace (s : ℝ) (g : Fin 4 → ℝ) : ∑ j, kappa s g j = 0 := by
  simp [kappa, Fin.sum_univ_succ]
  ring

theorem chart_inverse (v : Fin 6 → ℝ) (htrace : ∑ j, v j = 0) :
    kappa (v 0/5)
      ![(v 2-v 1)/5, (v 3-v 2)/5, (v 4-v 3)/5, (v 5-v 4)/5] = v := by
  have ht : v 0+v 1+v 2+v 3+v 4+v 5 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using htrace
  funext j
  fin_cases j <;> simp [kappa] <;> linarith

theorem sorted_representative (v : Fin 6 → ℝ) (i : Fin 6) :
    ∃ e : Equiv.Perm (Fin 6), e 0 = i ∧
      Monotone (fun a : Fin 5 => v (e a.succ)) := by
  let f : Fin 5 → ℝ := fun a => v (i.succAbove a)
  let e : Equiv.Perm (Fin 6) :=
    (finSuccEquiv' (0 : Fin 6)).trans
      ((Equiv.optionCongr (Tuple.sort f)).trans (finSuccEquiv' i).symm)
  have he0 : e 0 = i := by simp [e]
  have hes (a : Fin 5) : e a.succ = i.succAbove (Tuple.sort f a) := by
    simp [e, finSuccEquiv'_above]
  refine ⟨e, he0, ?_⟩
  intro a b hab
  simpa only [hes] using Tuple.monotone_sort f hab

end R7.SpectralChart
