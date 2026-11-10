import R7.Algebra.KernelPower
import Mathlib.Tactic.Ring

/-! Sparse Horner evaluation with a proof of its ordinary polynomial semantics. -/
namespace R7.Algebra.SparseHorner
open R7.Algebra.KernelPower

/-- Successive exponents are weakly decreasing, starting below `n`. -/
def OrderedFrom (n : ℕ) : List (ℕ × ℤ) → Prop
  | [] => True
  | (m, _) :: rest => m ≤ n ∧ OrderedFrom m rest

/-- The value of the sparse polynomial, independently of Horner evaluation. -/
def sum (base : ℤ) (terms : List (ℕ × ℤ)) : ℤ :=
  (terms.map (fun term => term.2 * base ^ term.1)).sum

/-- Executable sparse Horner evaluation using logarithmic exponentiation. -/
def eval (base : ℤ) (terms : List (ℕ × ℤ)) : ℤ :=
  match terms with
  | [] => 0
  | first :: tail =>
    let state := tail.foldl (fun (state : ℕ × ℤ) ec =>
      (ec.1, state.2 * fastPow base (state.1 - ec.1) + ec.2)) first
    state.2 * fastPow base state.1

theorem foldl_correct (base : ℤ) (terms : List (ℕ × ℤ)) (n : ℕ) (acc : ℤ)
    (h : OrderedFrom n terms) :
    let state := terms.foldl (fun (state : ℕ × ℤ) ec =>
      (ec.1, state.2 * fastPow base (state.1 - ec.1) + ec.2)) (n, acc)
    state.2 * fastPow base state.1 = acc * base ^ n + sum base terms := by
  induction terms generalizing n acc with
  | nil => simp [sum, fastPow_eq_pow]
  | cons term terms ih =>
    rcases term with ⟨m, c⟩
    obtain ⟨hm, ht⟩ := h
    simp only [List.foldl_cons]
    rw [ih m (acc * fastPow base (n - m) + c) ht]
    simp only [sum, List.map_cons, List.sum_cons, fastPow_eq_pow]
    have hp : base ^ (n - m) * base ^ m = base ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    calc
      (acc * base ^ (n - m) + c) * base ^ m +
          (List.map (fun term => term.2 * base ^ term.1) terms).sum =
          acc * (base ^ (n - m) * base ^ m) +
            (c * base ^ m + (List.map (fun term => term.2 * base ^ term.1) terms).sum) := by ring
      _ = _ := by rw [hp]

/-- Main correctness statement. Duplicate exponents are allowed. -/
theorem eval_eq_sum (base : ℤ) (terms : List (ℕ × ℤ))
    (h : ∀ first tail, terms = first :: tail → OrderedFrom first.1 tail) :
    eval base terms = sum base terms := by
  cases terms with
  | nil => simp [eval, sum]
  | cons first tail =>
    rw [eval, foldl_correct base tail first.1 first.2 (h first tail rfl)]
    simp [sum]

/-- The power-of-two version, matching the concrete Kronecker certificate. -/
def evalBits (bits : ℕ) (terms : List (ℕ × ℤ)) : ℤ :=
  match terms with
  | [] => 0
  | first :: tail =>
    let state := tail.foldl (fun (state : ℕ × ℤ) ec =>
      (ec.1, state.2 * fastPow (2 : ℤ) (bits * (state.1 - ec.1)) + ec.2)) first
    state.2 * fastPow (2 : ℤ) (bits * state.1)

theorem evalBits_eq_eval (bits : ℕ) (terms : List (ℕ × ℤ)) :
    evalBits bits terms = eval (fastPow (2 : ℤ) bits) terms := by
  have hp (n : ℕ) : fastPow (2 : ℤ) (bits * n) =
      fastPow (fastPow (2 : ℤ) bits) n := by
    simp only [fastPow_eq_pow, pow_mul]
  cases terms with
  | nil => rfl
  | cons first tail =>
    simp only [evalBits, eval]
    simp_rw [hp]

theorem evalBits_eq_sum (bits : ℕ) (terms : List (ℕ × ℤ))
    (h : ∀ first tail, terms = first :: tail → OrderedFrom first.1 tail) :
    evalBits bits terms =
      (terms.map (fun term => term.2 * (2 : ℤ) ^ (bits * term.1))).sum := by
  rw [evalBits_eq_eval, eval_eq_sum _ _ h]
  simp only [sum, fastPow_eq_pow, pow_mul]

end R7.Algebra.SparseHorner
