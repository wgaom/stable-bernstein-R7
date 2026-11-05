import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace R7.Core.Univariate

open scoped BigOperators

abbrev Poly := List ℚ

noncomputable def evaluate : Poly → ℝ → ℝ
  | [], _ => 0
  | a::p, x => a + x * evaluate p x

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def neg (p : Poly) : Poly := p.map (- ·)
def scale (a : ℚ) (p : Poly) : Poly := p.map (a * ·)
def mul : Poly → Poly → Poly
  | [], _ => []
  | a::p, q => add (scale a q) (0::mul p q)
def power (p : Poly) : ℕ → Poly
  | 0 => [1]
  | n+1 => mul (power p n) p

def equal (p q : Poly) : Bool := (add p (neg q)).all (· == 0)

@[simp] theorem evaluate_nil (x : ℝ) : evaluate [] x = 0 := rfl

@[simp] theorem evaluate_cons (a : ℚ) (p : Poly) (x : ℝ) :
    evaluate (a::p) x = a + x * evaluate p x := rfl

@[simp] theorem evaluate_add (p q : Poly) (x : ℝ) :
    evaluate (add p q) x = evaluate p x + evaluate q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih => cases q with
    | nil => simp [add]
    | cons b q => simp only [add, evaluate_cons, ih, Rat.cast_add]; ring

@[simp] theorem evaluate_neg (p : Poly) (x : ℝ) : evaluate (neg p) x = -evaluate p x := by
  induction p with
  | nil => simp [neg]
  | cons a p ih => simp only [neg, List.map_cons, evaluate_cons, Rat.cast_neg] at *; rw [ih]; ring

@[simp] theorem evaluate_scale (a : ℚ) (p : Poly) (x : ℝ) :
    evaluate (scale a p) x = a * evaluate p x := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change (a*b : ℚ) + x * evaluate (scale a p) x = _
    rw [evaluate_cons, ih, Rat.cast_mul]; ring

@[simp] theorem evaluate_mul (p q : Poly) (x : ℝ) :
    evaluate (mul p q) x = evaluate p x * evaluate q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp only [mul, evaluate_add, evaluate_scale, evaluate_cons, ih, Rat.cast_zero]; ring

@[simp] theorem evaluate_power (p : Poly) (n : ℕ) (x : ℝ) :
    evaluate (power p n) x = evaluate p x ^ n := by
  induction n with
  | zero => simp [power, evaluate]
  | succ n ih => simp [power, ih, pow_succ]

theorem equal_sound (p q : Poly) (h : equal p q = true) (x : ℝ) :
    evaluate p x = evaluate q x := by
  have hz (r : Poly) (h : r.all (· == 0) = true) : evaluate r x = 0 := by
    induction r with
    | nil => rfl
    | cons a r ih =>
      have hs : a = 0 ∧ r.all (· == 0) = true := by simpa using h
      simp [hs.1, ih hs.2]
  have he := hz (add p (neg q)) h
  simpa only [evaluate_add, evaluate_neg, ← sub_eq_add_neg, sub_eq_zero] using he

def sum : List Poly → Poly
  | [] => []
  | p::ps => add p (sum ps)

@[simp] theorem evaluate_sum (ps : List Poly) (x : ℝ) :
    evaluate (sum ps) x = (ps.map (fun p => evaluate p x)).sum := by
  induction ps <;> simp_all [sum]

def compactPolynomial (n : ℕ) (a b : ℚ) (c : Fin (n+1) → ℚ) : Poly :=
  sum ((List.finRange (n+1)).map fun j =>
    mul (mul [c j] (power [-a,1] j)) (power [b,-1] (n-j)))

@[simp] theorem evaluate_compactPolynomial (n : ℕ) (a b : ℚ)
    (c : Fin (n+1) → ℚ) (x : ℝ) :
    evaluate (compactPolynomial n a b c) x =
      ∑ j, (c j : ℝ) * (x - a) ^ (j : ℕ) * (b - x) ^ (n-j) := by
  unfold compactPolynomial
  rw [← List.ofFn_eq_map, evaluate_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp [evaluate, sub_eq_add_neg, add_comm]

theorem compactPolynomial_pos (n : ℕ) (a b : ℚ) (c : Fin (n+1) → ℚ)
    (hab : a < b) (hc : ∀ j, 0 < c j) (x : ℝ)
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    0 < evaluate (compactPolynomial n a b c) x := by
  rw [evaluate_compactPolynomial]
  have hcR (j) : (0 : ℝ) < c j := by exact_mod_cast hc j
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (mul_nonneg (le_of_lt (hcR j))
      (pow_nonneg (sub_nonneg.mpr ha) _)) (pow_nonneg (sub_nonneg.mpr hb) _)
  · by_cases hxb : x < (b : ℝ)
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simpa using mul_pos (hcR 0) (pow_pos (sub_pos.mpr hxb) n)
    · have hxeq : x = (b : ℝ) := le_antisymm hb (le_of_not_gt hxb)
      refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one]
      exact mul_pos (hcR (Fin.last n)) (pow_pos (by linarith) n)

inductive CompactCertificate where
  | leaf (n : ℕ) (coefficients : Fin (n+1) → ℚ)
  | split (mid : ℚ) (left right : CompactCertificate)

def checkCompact (p : Poly) (a b : ℚ) : CompactCertificate → Bool
  | .leaf n c => decide (a < b ∧ ∀ j, 0 < c j) && equal p (compactPolynomial n a b c)
  | .split mid left right => checkCompact p a mid left && checkCompact p mid b right

theorem checkCompact_sound (p : Poly) (a b : ℚ) (certificate : CompactCertificate)
    (h : checkCompact p a b certificate = true) (x : ℝ)
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) : 0 < evaluate p x := by
  induction certificate generalizing a b with
  | leaf n c =>
    have hs := Bool.and_eq_true_iff.mp h
    have hc : a < b ∧ ∀ j, 0 < c j := of_decide_eq_true hs.1
    rw [equal_sound _ _ hs.2 x]
    exact compactPolynomial_pos n a b c hc.1 hc.2 x ha hb
  | split mid left right ihl ihr =>
    have hs := Bool.and_eq_true_iff.mp h
    rcases le_total x (mid : ℝ) with hxm | hmx
    · exact ihl a mid hs.1 ha hxm
    · exact ihr mid b hs.2 hmx hb

def compactify : Poly → ℕ → Poly
  | [], _ => []
  | a::_, 0 => [a]
  | a::p, n+1 => add (scale a (power [1,-1] (n+1)))
      (mul [0,1] (compactify p n))

theorem compactify_scaling (p : Poly) (n : ℕ) (hdegree : p.length ≤ n+1)
    (x t z : ℝ) (hzt : z*t=x) (hz1 : z*(1-t)=1) :
    z^n * evaluate (compactify p n) t = evaluate p x := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [compactify]
    | cons a p =>
      have hp : p = [] := List.eq_nil_of_length_eq_zero (by simpa using hdegree)
      subst p
      simp [compactify, evaluate]
  | succ n ih =>
    cases p with
    | nil => simp [compactify]
    | cons a p =>
      have hp : p.length ≤ n+1 := by simpa using hdegree
      have he : evaluate (compactify (a::p) (n+1)) t =
          (a : ℝ)*(1-t)^(n+1)+t*evaluate (compactify p n) t := by
        simp [compactify, evaluate, sub_eq_add_neg]
      rw [he]
      calc
        z^(n+1)*((a : ℝ)*(1-t)^(n+1)+t*evaluate (compactify p n) t) =
            (a : ℝ)*(z*(1-t))^(n+1)+(z*t)*(z^n*evaluate (compactify p n) t) := by
          rw [mul_pow, pow_succ z]
          ring
        _ = evaluate (a::p) x := by rw [hz1, hzt, ih p hp]; simp [evaluate]

def checkCompactified (p : Poly) (n : ℕ) (certificate : CompactCertificate) : Bool :=
  decide (p.length ≤ n+1) && checkCompact (compactify p n) 0 1 certificate

theorem checkCompactified_sound (p : Poly) (n : ℕ) (certificate : CompactCertificate)
    (h : checkCompactified p n certificate = true) :
    ∀ x : ℝ, 0 ≤ x → 0 < evaluate p x := by
  intro x hx
  have hs := Bool.and_eq_true_iff.mp h
  have hd : p.length ≤ n+1 := of_decide_eq_true hs.1
  have hz : 0 < 1+x := by linarith
  have ht0 : 0 ≤ x/(1+x) := div_nonneg hx (le_of_lt hz)
  have ht1 : x/(1+x) ≤ 1 := (div_le_one hz).mpr (by linarith)
  have he := checkCompact_sound (compactify p n) 0 1 certificate hs.2
    (x/(1+x)) (by simpa using ht0) (by simpa using ht1)
  have hzt : (1+x)*(x/(1+x))=x := by field_simp
  have hz1 : (1+x)*(1-x/(1+x))=1 := by field_simp; ring
  rw [← compactify_scaling p n hd x (x/(1+x)) (1+x) hzt hz1]
  exact mul_pos (pow_pos hz n) he

end R7.Core.Univariate
