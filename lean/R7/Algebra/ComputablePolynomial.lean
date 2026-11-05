import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.List.Defs
import Mathlib.Data.Finsupp.Fintype

namespace R7.ComputablePolynomial
abbrev Exp := Fin 5 → ℕ
abbrev Poly := List (Exp × ℚ)

def indeterminate (i : Fin 5) : Poly := [(fun j => if j=i then 1 else 0,1)]

noncomputable def exponent (e : Exp) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm e

noncomputable def interpret : Poly → MvPolynomial (Fin 5) ℚ
  | [] => 0
  | (e,a)::tail => MvPolynomial.monomial (exponent e) a + interpret tail

@[simp] theorem exponent_zero : exponent 0 = 0 := by
  ext i; simp [exponent]
@[simp] theorem exponent_add (e f : Exp) : exponent (e+f) = exponent e+exponent f := by
  ext i; simp [exponent]

@[simp] theorem interpret_variable (i : Fin 5) : interpret (indeterminate i) = MvPolynomial.X i := by
  have he : exponent (fun j => if j=i then 1 else 0) = Finsupp.single i 1 := by
    ext j; by_cases hj : j=i <;> simp [exponent,hj]
  simp [indeterminate,interpret,he,MvPolynomial.X]

inductive Expr where
  | rat : ℚ → Expr
  | var : Fin 5 → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → ℕ → Expr

noncomputable def Expr.denote : Expr → MvPolynomial (Fin 5) ℚ
  | .rat a => MvPolynomial.C a
  | .var i => MvPolynomial.X i
  | .add a b => a.denote+b.denote
  | .neg a => -a.denote
  | .mul a b => a.denote*b.denote
  | .pow a n => a.denote^n

end R7.ComputablePolynomial
