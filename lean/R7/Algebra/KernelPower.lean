import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Init
import Lean.Elab.Tactic.Omega

/-! Kernel-computable binary exponentiation, with a monoid-generic correctness proof. -/
namespace R7.Algebra.KernelPower

/-- Exponentiation using at most logarithmically many recursive calls. -/
def fastPow {α : Type*} [Monoid α] (a : α) (n : ℕ) : α :=
  if n = 0 then 1
  else
    let b := fastPow a (n / 2)
    if n % 2 = 0 then b * b else b * b * a
termination_by n
decreasing_by omega

theorem fastPow_eq_pow {α : Type*} [Monoid α] (a : α) (n : ℕ) :
    fastPow a n = a ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fastPow]
    split_ifs with hn heven
    · subst n
      simp
    · rw [ih (n / 2) (by omega)]
      dsimp only
      rw [← pow_add]
      have h : n / 2 + n / 2 = n := by omega
      rw [h]
    · rw [ih (n / 2) (by omega)]
      dsimp only
      rw [← pow_add, ← pow_succ]
      have h : n / 2 + n / 2 + 1 = n := by omega
      rw [h]

end R7.Algebra.KernelPower
