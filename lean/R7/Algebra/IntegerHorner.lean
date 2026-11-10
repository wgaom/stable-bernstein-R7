import R7.Algebra.IntegerExpression
import R7.Algebra.KernelPower
import R7.Algebra.SparseHorner
import Mathlib.Algebra.Polynomial.Roots

namespace R7.Algebra.IntegerHorner
open R7.Algebra.Kronecker

/-- Kernel efficient evaluation, including large Kronecker powers. -/
def evaluate (B : ℤ) : Expr → ℤ
  | .constant c => c
  | .variable n => R7.Algebra.KernelPower.fastPow B n
  | .add a b => evaluate B a+evaluate B b
  | .neg a => -evaluate B a
  | .mul a b => evaluate B a*evaluate B b
  | .pow a n => R7.Algebra.KernelPower.fastPow (evaluate B a) n

@[simp] theorem evaluate_correct (B : ℤ) (e : Expr) : evaluate B e = e.evaluate B := by
  induction e <;> simp_all [evaluate,Expr.evaluate,R7.Algebra.KernelPower.fastPow_eq_pow]

/-- Sparse Horner syntax, whose coefficient bound is just sum of coefficient
absolute values. Descending keys are supplied as untrusted certificate data. -/
def horner (terms : List (ℕ × ℤ)) : Expr :=
  match terms with
  | [] => .constant 0
  | first::tail =>
    let state := tail.foldl (fun (state : ℕ × Expr) ec =>
      (ec.1,.add (.mul state.2 (.variable (state.1-ec.1))) (.constant ec.2)))
      (first.1,.constant first.2)
    .mul state.2 (.variable state.1)

lemma evaluate_horner (B : ℤ) (terms : List (ℕ × ℤ)) :
    (horner terms).evaluate B = R7.Algebra.SparseHorner.eval B terms := by
  cases terms with
  | nil => rfl
  | cons first tail =>
    simp only [horner,R7.Algebra.SparseHorner.eval]
    simp_rw [R7.Algebra.KernelPower.fastPow_eq_pow]
    have h := List.foldl_hom (fun state : ℕ × Expr => (state.1,state.2.evaluate B))
      (g₁ := fun state ec => (ec.1,Expr.add (Expr.mul state.2 (Expr.variable (state.1-ec.1))) (Expr.constant ec.2)))
      (g₂ := fun state ec => (ec.1,state.2*B^(state.1-ec.1)+ec.2))
      (l := tail) (init := (first.1,Expr.constant first.2)) (by intro state ec; rfl)
    exact (congrArg (fun state : ℕ × ℤ => state.2*B^state.1) h).symm

lemma denote_horner (terms : List (ℕ × ℤ))
    (h : ∀ first tail, terms=first::tail → R7.Algebra.SparseHorner.OrderedFrom first.1 tail) :
    (horner terms).denote = R7.Algebra.Kronecker.polynomial terms := by
  apply Polynomial.funext
  intro B
  rw [R7.Algebra.Kronecker.Expr.evaluate_correct, evaluate_horner, R7.Algebra.SparseHorner.eval_eq_sum B terms h]
  have hh (ts : List (ℕ × ℤ)) : (R7.Algebra.Kronecker.polynomial ts).eval B = R7.Algebra.SparseHorner.sum B ts := by
    induction ts with
    | nil => simp [R7.Algebra.SparseHorner.sum,R7.Algebra.Kronecker.polynomial]
    | cons ec tail ih => simp [R7.Algebra.SparseHorner.sum,R7.Algebra.Kronecker.polynomial,Polynomial.eval_monomial,ih]
  exact (hh terms).symm

end R7.Algebra.IntegerHorner
