import R7.Algebra.Kronecker
import R7.Algebra.KernelPower

/-! Generic integer polynomial expressions, structural coefficient bounds and
exact one-point identity certificates. This module has no rational five-variable
AST or spectral dependencies. -/
namespace R7.Algebra.Kronecker
open Polynomial
abbrev Terms := List (ℕ × ℤ)

def mass : Terms → ℤ
  | [] => 0
  | (_,c)::tail => |c| + mass tail

noncomputable def polynomial : Terms → Polynomial ℤ
  | [] => 0
  | (n,c)::tail => Polynomial.monomial n c + polynomial tail

def scaled (c : ℤ) (a : Terms) : Terms := a.map (fun nc => (nc.1,c*nc.2))
def times (a b : Terms) : Terms :=
  a.flatMap (fun nc => b.map (fun md => (nc.1+md.1,nc.2*md.2)))

@[simp] theorem mass_nonneg (a : Terms) : 0 ≤ mass a := by
  induction a with
  | nil => rfl
  | cons a tail ih => exact add_nonneg (abs_nonneg _) ih

@[simp] theorem mass_append (a b : Terms) : mass (a++b) = mass a + mass b := by
  induction a with
  | nil => simp [mass]
  | cons nc tail ih => simp [mass,ih,add_assoc]

@[simp] theorem polynomial_append (a b : Terms) :
    polynomial (a++b) = polynomial a + polynomial b := by
  induction a with
  | nil => simp [polynomial]
  | cons nc tail ih => simp [polynomial,ih,add_assoc]

@[simp] theorem mass_scaled (c : ℤ) (a : Terms) : mass (scaled c a) = |c| * mass a := by
  induction a with
  | nil => simp [mass,scaled]
  | cons nc tail ih =>
    change |c*nc.2| + mass (scaled c tail) = _
    simp only [ih,abs_mul,mass,mul_add]

@[simp] theorem polynomial_scaled (c : ℤ) (a : Terms) :
    polynomial (scaled c a) = Polynomial.C c * polynomial a := by
  induction a with
  | nil => simp [polynomial,scaled]
  | cons nc tail ih =>
    change Polynomial.monomial nc.1 (c*nc.2) + polynomial (scaled c tail) = _
    simp only [ih,polynomial,mul_add,C_mul_monomial]

private theorem mass_shifted (n : ℕ) (c : ℤ) (a : Terms) :
    mass (a.map (fun md => (n+md.1,c*md.2))) = |c| * mass a := by
  induction a with
  | nil => simp [mass]
  | cons md tail ih => simp [mass,abs_mul,mul_add,ih]

private theorem polynomial_shifted (n : ℕ) (c : ℤ) (a : Terms) :
    polynomial (a.map (fun md => (n+md.1,c*md.2))) =
      Polynomial.monomial n c * polynomial a := by
  induction a with
  | nil => simp [polynomial]
  | cons md tail ih => simp [polynomial,mul_add,ih,monomial_mul_monomial]

@[simp] theorem mass_times (a b : Terms) : mass (times a b) = mass a*mass b := by
  induction a with
  | nil => simp [times,mass]
  | cons nc tail ih =>
    change mass ((b.map (fun md => (nc.1+md.1,nc.2*md.2))) ++ times tail b) = _
    rw [mass_append,mass_shifted,ih]
    simp [mass,add_mul]

@[simp] theorem polynomial_times (a b : Terms) :
    polynomial (times a b) = polynomial a * polynomial b := by
  induction a with
  | nil => simp [times,polynomial]
  | cons nc tail ih =>
    change polynomial ((b.map (fun md => (nc.1+md.1,nc.2*md.2))) ++ times tail b) = _
    rw [polynomial_append,polynomial_shifted,ih]
    simp [polynomial,add_mul]

/-- Raw distributive mass bounds every normalized coefficient, even when raw
terms cancel or contain repeated exponents. -/
theorem coefficient_abs_le_mass (a : Terms) (n : ℕ) :
    |(polynomial a).coeff n| ≤ mass a := by
  induction a with
  | nil => simp [polynomial,mass]
  | cons nc tail ih =>
    simp only [polynomial,coeff_add,mass]
    apply (abs_add_le _ _).trans
    apply add_le_add _ ih
    simp only [coeff_monomial]
    split_ifs <;> simp

/-- Integer polynomial expressions admit an inexpensive structural bound. -/
inductive Expr where
  | constant : ℤ → Expr
  | variable : ℕ → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → ℕ → Expr

def Expr.bound : Expr → ℤ
  | .constant c => |c|
  | .variable _ => 1
  | .add a b => a.bound+b.bound
  | .neg a => a.bound
  | .mul a b => a.bound*b.bound
  | .pow a n => a.bound^n

def powerTerms (a : Terms) : ℕ → Terms
  | 0 => [(0,1)]
  | n+1 => times (powerTerms a n) a

def Expr.terms : Expr → Terms
  | .constant c => [(0,c)]
  | .variable n => [(n,1)]
  | .add a b => a.terms++b.terms
  | .neg a => scaled (-1) a.terms
  | .mul a b => times a.terms b.terms
  | .pow a n => powerTerms a.terms n

@[simp] theorem mass_powerTerms (a : Terms) (n : ℕ) : mass (powerTerms a n) = mass a ^ n := by
  induction n with
  | zero => simp [powerTerms,mass]
  | succ n ih => simp [powerTerms,ih,pow_succ]

@[simp] theorem Expr.mass_terms (e : Expr) : mass e.terms = e.bound := by
  induction e <;> simp_all [Expr.terms,Expr.bound,mass]

noncomputable def Expr.denote : Expr → Polynomial ℤ
  | .constant c => Polynomial.C c
  | .variable n => Polynomial.X^n
  | .add a b => a.denote+b.denote
  | .neg a => -a.denote
  | .mul a b => a.denote*b.denote
  | .pow a n => a.denote^n

@[simp] theorem polynomial_powerTerms (a : Terms) (n : ℕ) :
    polynomial (powerTerms a n) = polynomial a ^ n := by
  induction n with
  | zero => simp [powerTerms,polynomial,monomial_zero_left]
  | succ n ih => simp [powerTerms,ih,pow_succ]

@[simp] theorem Expr.polynomial_terms (e : Expr) : polynomial e.terms = e.denote := by
  induction e <;> simp_all [Expr.terms,Expr.denote,polynomial,monomial_zero_left,monomial_one_right_eq_X_pow]

/-- Universal bound: no concrete distributive expansion needs to run. -/
theorem Expr.coefficient_bound (e : Expr) (n : ℕ) : |e.denote.coeff n| ≤ e.bound := by
  simpa only [Expr.polynomial_terms, Expr.mass_terms] using coefficient_abs_le_mass e.terms n

/-- Direct evaluation is structural and does not construct a term list. -/
def Expr.evaluate (x : ℤ) : Expr → ℤ
  | .constant c => c
  | .variable n => x^n
  | .add a b => a.evaluate x+b.evaluate x
  | .neg a => -a.evaluate x
  | .mul a b => a.evaluate x*b.evaluate x
  | .pow a n => (a.evaluate x)^n

@[simp] theorem Expr.evaluate_correct (e : Expr) (x : ℤ) : e.denote.eval x = e.evaluate x := by
  induction e <;> simp_all [Expr.denote,Expr.evaluate]

/-- The structural coefficient bound makes a single structural integer
calculation an exact identity proof for two AST expressions. -/
theorem Expr.identity_of_evaluation (a b : Expr) {B : ℤ}
    (hb : a.bound+b.bound < B) (he : a.evaluate B = b.evaluate B) : a.denote=b.denote := by
  have ha0 : 0 ≤ a.bound := by rw [← a.mass_terms]; exact mass_nonneg _
  have hb0 : 0 ≤ b.bound := by rw [← b.mass_terms]; exact mass_nonneg _
  apply R7.Algebra.Kronecker.eq_of_eval_eq (B := B) (by omega) a.denote b.denote
  · intro n
    exact lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add (a.coefficient_bound n) (b.coefficient_bound n))) hb
  · simpa only [Expr.evaluate_correct] using he

/-- Structural evaluation using binary exponentiation. -/
def Expr.evaluateFast (x : ℤ) : Expr → ℤ
  | .constant c => c
  | .variable n => R7.Algebra.KernelPower.fastPow x n
  | .add a b => a.evaluateFast x+b.evaluateFast x
  | .neg a => -a.evaluateFast x
  | .mul a b => a.evaluateFast x*b.evaluateFast x
  | .pow a n => R7.Algebra.KernelPower.fastPow (a.evaluateFast x) n

@[simp] theorem Expr.evaluateFast_correct (e : Expr) (x : ℤ) :
    e.evaluateFast x = e.evaluate x := by
  induction e <;> simp_all [Expr.evaluateFast,Expr.evaluate,R7.Algebra.KernelPower.fastPow_eq_pow]

end R7.Algebra.Kronecker
