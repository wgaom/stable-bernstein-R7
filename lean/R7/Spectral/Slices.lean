import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

noncomputable section
namespace R7.Core.SpectralSlices
open scoped BigOperators

abbrev GapExponent := Fin 4 → ℕ

def point (z : ℝ) (g : Fin 4 → ℝ) : Fin 5 → ℝ := Fin.cons z g

def gapMonomial (β : GapExponent) (g : Fin 4 → ℝ) : ℝ := ∏ j, g j ^ β j

theorem gapMonomial_nonneg (β : GapExponent) (g : Fin 4 → ℝ)
    (hg : ∀ j, 0 ≤ g j) : 0 ≤ gapMonomial β g :=
 Finset.prod_nonneg fun j _ => pow_nonneg (hg j) _

end R7.Core.SpectralSlices
