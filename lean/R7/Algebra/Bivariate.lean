import R7.Algebra.Univariate

namespace R7.Core.Bivariate
open R7.Core.Univariate
abbrev BiPoly := List Poly

noncomputable def eval : BiPoly → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a::p, x, y => evaluate a y+x*eval p x y

def add : BiPoly → BiPoly → BiPoly
  | [], q => q
  | p, [] => p
  | a::p,b::q => Univariate.add a b::add p q

def neg (p : BiPoly) : BiPoly := p.map Univariate.neg
def scale (a : ℚ) (p : BiPoly) : BiPoly := p.map (Univariate.scale a)
def mul : BiPoly → BiPoly → BiPoly
  | [], _ => []
  | a::p,q => add (q.map (Univariate.mul a)) ([]::mul p q)
def power (p : BiPoly) : ℕ → BiPoly
  | 0 => [[1]]
  | n+1 => mul (power p n) p

def C (a : ℚ) : BiPoly := [[a]]
def xx : BiPoly := [[],[1]]
def yy : BiPoly := [[0,1]]
def sub (p q : BiPoly) : BiPoly := add p (neg q)
def equal (p q : BiPoly) : Bool := (add p (neg q)).all (fun a => a.all (· == 0))

@[simp] theorem eval_add (p q : BiPoly) (x y : ℝ) :
    eval (add p q) x y = eval p x y+eval q x y := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih => cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,evaluate_add,ih]; ring

@[simp] theorem eval_neg (p : BiPoly) (x y : ℝ) : eval (neg p) x y = -eval p x y := by
  induction p with
  | nil => simp [neg,eval]
  | cons a p ih => simp only [neg,List.map_cons,eval,evaluate_neg] at *; rw [ih]; ring

@[simp] theorem eval_scale (a : ℚ) (p : BiPoly) (x y : ℝ) :
    eval (scale a p) x y = a*eval p x y := by
  induction p with
  | nil => simp [scale,eval]
  | cons b p ih => simp only [scale,List.map_cons,eval,evaluate_scale] at *; rw [ih]; ring

theorem eval_map_mul (a : Poly) (q : BiPoly) (x y : ℝ) :
    eval (q.map (Univariate.mul a)) x y = evaluate a y*eval q x y := by
  induction q with
  | nil => simp [eval]
  | cons b q ih => simp only [List.map_cons,eval,evaluate_mul,ih]; ring

@[simp] theorem eval_mul (p q : BiPoly) (x y : ℝ) :
    eval (mul p q) x y = eval p x y*eval q x y := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => simp only [mul,eval_add,eval_map_mul,eval,evaluate_nil,ih]; ring

@[simp] theorem eval_power (p : BiPoly) (n : ℕ) (x y : ℝ) :
    eval (power p n) x y = eval p x y^n := by
  induction n with
  | zero => simp [power,eval,evaluate]
  | succ n ih => simp [power,ih,pow_succ]

@[simp] theorem eval_C (a : ℚ) (x y : ℝ) : eval (C a) x y = a := by simp [C,eval,evaluate]
@[simp] theorem eval_xx (x y : ℝ) : eval xx x y = x := by simp [xx,eval,evaluate]
@[simp] theorem eval_yy (x y : ℝ) : eval yy x y = y := by simp [yy,eval,evaluate]
@[simp] theorem eval_sub (p q : BiPoly) (x y : ℝ) :
    eval (sub p q) x y = eval p x y-eval q x y := by simp [sub,sub_eq_add_neg]

theorem evaluate_zero (a : Poly) (h : a.all (· == 0) = true) (y : ℝ) :
    evaluate a y = 0 := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    have hh : c = 0 ∧ a.all (· == 0) = true := by simpa using h
    simp [hh.1,ih hh.2]

theorem equal_sound (p q : BiPoly) (h : equal p q = true) (x y : ℝ) :
    eval p x y = eval q x y := by
  have hz (r : BiPoly) (h : r.all (fun a => a.all (· == 0)) = true) : eval r x y = 0 := by
    induction r with
    | nil => rfl
    | cons a r ih =>
      have hs : a.all (· == 0) = true ∧ r.all (fun a => a.all (· == 0)) = true := by simpa using h
      have ha : evaluate a y = 0 := evaluate_zero a hs.1 y
      simp only [eval,ha,ih hs.2,mul_zero,add_zero]
  have hh := hz (add p (neg q)) h
  simpa only [eval_add,eval_neg,← sub_eq_add_neg,sub_eq_zero] using hh

end R7.Core.Bivariate
