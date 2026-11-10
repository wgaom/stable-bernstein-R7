import R7.Algebra.PositiveLeaf
import Mathlib.Data.Rat.Lemmas

namespace R7.Core.Univariate.IntegerCompact
open R7.Core.Univariate
open scoped BigOperators

abbrev ZPoly := List ℤ
noncomputable def evalZ : ZPoly → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * evalZ p x

def addZ : ZPoly → ZPoly → ZPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: addZ p q

def scaleZ (a : ℤ) (p : ZPoly) : ZPoly := p.map (a * ·)

def linearZ (a b : ℤ) (p : ZPoly) : ZPoly :=
  addZ (scaleZ a p) (0 :: scaleZ b p)

@[simp] theorem evalZ_add (p q : ZPoly) (x : ℝ) :
    evalZ (addZ p q) x = evalZ p x + evalZ q x := by
  induction p generalizing q with
  | nil => simp [addZ, evalZ]
  | cons a p ih => cases q with
    | nil => simp [addZ, evalZ]
    | cons b q => simp only [addZ, evalZ, ih, Int.cast_add]; ring

@[simp] theorem evalZ_scale (a : ℤ) (p : ZPoly) (x : ℝ) :
    evalZ (scaleZ a p) x = a * evalZ p x := by
  induction p with
  | nil => simp [scaleZ, evalZ]
  | cons b p ih => simp only [scaleZ, List.map_cons, evalZ, Int.cast_mul] at *; rw [ih]; ring

@[simp] theorem evalZ_linear (a b : ℤ) (p : ZPoly) (x : ℝ) :
    evalZ (linearZ a b p) x = (a + b*x) * evalZ p x := by
  simp [linearZ, evalZ]; ring

/-- Integer homogeneous Bernstein expansion with two arbitrary linear factors. -/
def compactPairZ (A B D : ℤ) : (n : ℕ) → (Fin (n+1) → ℤ) → ZPoly × ZPoly
  | 0, c => ([c 0], [1])
  | n+1, c =>
      let prev := compactPairZ A B D n (fun j => c j.succ)
      let secondPower := linearZ B (-D) prev.2
      (addZ (scaleZ (c 0) secondPower) (linearZ (-A) D prev.1), secondPower)

theorem evalZ_compactPair (A B D : ℤ) (n : ℕ) (c : Fin (n+1) → ℤ) (x : ℝ) :
    evalZ (compactPairZ A B D n c).1 x =
      ∑ j, (c j : ℝ) * (D*x-A)^j.val * (B-D*x)^(n-j.val) ∧
    evalZ (compactPairZ A B D n c).2 x = (B-D*x)^n := by
  induction n with
  | zero => simp [compactPairZ, evalZ]
  | succ n ih =>
      have hp := ih (fun j => c j.succ)
      constructor
      · simp only [compactPairZ, evalZ_add, evalZ_scale, evalZ_linear, Int.cast_neg,
          hp.1, hp.2]
        conv_rhs => rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, Nat.sub_zero, Fin.val_succ,
          Nat.add_sub_add_right]
        rw [pow_succ]
        congr 1
        · ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_succ]
          ring
      · simp only [compactPairZ, evalZ_linear, Int.cast_neg, hp.2]
        rw [pow_succ]
        ring

/-- An integer coefficient is recoverable from the numerator once den=1. -/
theorem cast_num_eq (q : ℚ) (h : q.den = 1) : (q.num : ℝ) = q := by
  exact_mod_cast Rat.coe_int_num_of_den_eq_one h

@[simp] theorem evalZ_map_cast (p : ZPoly) (x : ℝ) :
    evaluate (p.map (fun (a : ℤ) => (a : ℚ))) x = evalZ p x := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.map_cons, evaluate_cons, evalZ, Rat.cast_intCast, ih]

theorem evalZ_map_num (p : Poly) (h : ∀ a ∈ p, a.den = 1) (x : ℝ) :
    evalZ (p.map Rat.num) x = evaluate p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      have ha := h a (by simp)
      have hp : ∀ b ∈ p, b.den = 1 := by intro b hb; exact h b (by simp [hb])
      simp only [List.map_cons, evalZ, evaluate_cons, cast_num_eq a ha, ih hp]

/-- Coefficientwise equality of dense polynomials. -/
def equalZ : ZPoly → ZPoly → Bool
  | [], q => q.all (· == 0)
  | p, [] => p.all (· == 0)
  | a::p, b::q => (a == b) && equalZ p q

theorem equalZ_sound (p q : ZPoly) (h : equalZ p q = true) (x : ℝ) :
    evalZ p x = evalZ q x := by
  have hz (r : ZPoly) (hr : r.all (· == 0) = true) : evalZ r x = 0 := by
    induction r with
    | nil => rfl
    | cons a r ih =>
        have hs : a = 0 ∧ r.all (· == 0) = true := by simpa using hr
        simp [evalZ, hs.1, ih hs.2]
  induction p generalizing q with
  | nil => simpa [evalZ] using (hz q h).symm
  | cons a p ih =>
      cases q with
      | nil => simpa [evalZ] using hz (a::p) h
      | cons b q =>
          have hs := Bool.and_eq_true_iff.mp h
          have hab : a = b := by simpa using hs.1
          simp only [evalZ, hab, ih q hs.2]

def denominator (a b : ℚ) : ℤ := (a.den * b.den : ℕ)
def leftNumerator (a b : ℚ) : ℤ := a.num * (b.den : ℤ)
def rightNumerator (a b : ℚ) : ℤ := b.num * (a.den : ℤ)

theorem denominator_pos (a b : ℚ) : 0 < denominator a b := by
  change (0 : ℤ) < (a.den * b.den : ℕ)
  exact_mod_cast Nat.mul_pos a.pos b.pos

theorem real_den_mul (a : ℚ) : (a.den : ℝ) * (a : ℝ) = (a.num : ℝ) := by
  have hd : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  rw [Rat.cast_def]
  field_simp

theorem leftNumerator_eq (a b : ℚ) :
    (leftNumerator a b : ℝ) = (denominator a b : ℝ) * (a : ℝ) := by
  simp only [leftNumerator, denominator, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [← real_den_mul a]
  ring

theorem rightNumerator_eq (a b : ℚ) :
    (rightNumerator a b : ℝ) = (denominator a b : ℝ) * (b : ℝ) := by
  simp only [rightNumerator, denominator, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [← real_den_mul b]
  ring

theorem compactPairZ_scaled (n : ℕ) (a b : ℚ) (c : Fin (n+1) → ℚ)
    (hc : ∀ j, (c j).den = 1) (x : ℝ) :
    evalZ (compactPairZ (leftNumerator a b) (rightNumerator a b) (denominator a b)
      n (fun j => (c j).num)).1 x =
      (denominator a b : ℝ)^n * evaluate (compactPolynomial n a b c) x := by
  rw [(evalZ_compactPair _ _ _ n (fun j => (c j).num) x).1,
    evaluate_compactPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [cast_num_eq (c j) (hc j), leftNumerator_eq, rightNumerator_eq]
  have ha : (denominator a b : ℝ)*x - (denominator a b : ℝ)*(a : ℝ) =
      (denominator a b : ℝ)*(x-a) := by ring
  have hb : (denominator a b : ℝ)*(b : ℝ) - (denominator a b : ℝ)*x =
      (denominator a b : ℝ)*(b-x) := by ring
  rw [ha, hb, mul_pow, mul_pow]
  have hp : (denominator a b : ℝ)^j.val * (denominator a b : ℝ)^(n-j.val) =
      (denominator a b : ℝ)^n := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ j.isLt)]
  calc
    (c j : ℝ) * ((denominator a b : ℝ)^j.val * (x-a)^j.val) *
        ((denominator a b : ℝ)^(n-j.val) * (b-x)^(n-j.val)) =
      ((denominator a b : ℝ)^j.val * (denominator a b : ℝ)^(n-j.val)) *
        ((c j : ℝ) * (x-a)^j.val * (b-x)^(n-j.val)) := by ring
    _ = _ := by rw [hp]

def checkIntegerCompact (p : ZPoly) (a b : ℚ) : CompactCertificate → Bool
  | .leaf n c =>
      decide (a < b ∧ ∀ j, 0 < c j) &&
      (List.finRange (n+1)).all (fun j => (c j).den == 1) &&
      equalZ (scaleZ ((denominator a b)^n) p)
        (compactPairZ (leftNumerator a b) (rightNumerator a b) (denominator a b)
          n (fun j => (c j).num)).1
  | .split mid left right =>
      checkIntegerCompact p a mid left && checkIntegerCompact p mid b right

theorem checkIntegerCompact_transfer
    (complete : ∀ p q : Poly, (∀ x : ℝ, evaluate p x = evaluate q x) → equal p q = true)
    (p : ZPoly) (q : Poly) (heval : ∀ x : ℝ, evalZ p x = evaluate q x)
    (a b : ℚ) (certificate : CompactCertificate)
    (h : checkIntegerCompact p a b certificate = true) :
    checkCompact q a b certificate = true := by
  induction certificate generalizing a b with
  | leaf n c =>
      have hs := Bool.and_eq_true_iff.mp h
      have hg := Bool.and_eq_true_iff.mp hs.1
      have hc : ∀ j, (c j).den = 1 := by
        intro j
        have hi := (List.all_eq_true.mp hg.2) j (List.mem_finRange j)
        simpa using hi
      apply Bool.and_eq_true_iff.mpr
      refine ⟨hg.1, complete q (compactPolynomial n a b c) ?_⟩
      intro x
      have hz := equalZ_sound _ _ hs.2 x
      rw [evalZ_scale, Int.cast_pow, compactPairZ_scaled n a b c hc] at hz
      have hd : 0 < (denominator a b : ℝ) := by exact_mod_cast denominator_pos a b
      have he := mul_left_cancel₀ (pow_ne_zero n (ne_of_gt hd)) hz
      exact (heval x).symm.trans he
  | split mid left right ihl ihr =>
      have hs := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨ihl a mid hs.1, ihr mid b hs.2⟩

def linearPowerZ (a b : ℤ) : ℕ → ZPoly
  | 0 => [1]
  | n+1 => linearZ a b (linearPowerZ a b n)

@[simp] theorem evalZ_linearPower (a b : ℤ) (n : ℕ) (x : ℝ) :
    evalZ (linearPowerZ a b n) x = (a+b*x)^n := by
  induction n with
  | zero => simp [linearPowerZ, evalZ]
  | succ n ih => simp only [linearPowerZ, evalZ_linear, ih]; rw [pow_succ]; ring

def compactifyPairZ : ZPoly → ℕ → ZPoly × ZPoly
  | [], n => ([], linearPowerZ 1 (-1) n)
  | a::_, 0 => ([a], [1])
  | a::p, n+1 =>
      let prev := compactifyPairZ p n
      let secondPower := linearZ 1 (-1) prev.2
      (addZ (scaleZ a secondPower) (0 :: prev.1), secondPower)

theorem evalZ_compactifyPair (p : ZPoly) (n : ℕ) (x : ℝ) :
    evalZ (compactifyPairZ p n).1 x =
      evaluate (compactify (p.map (fun (a : ℤ) => (a : ℚ))) n) x ∧
    evalZ (compactifyPairZ p n).2 x = (1-x)^n := by
  induction n generalizing p with
  | zero => cases p <;> simp [compactifyPairZ, compactify, evalZ, evaluate]
  | succ n ih =>
      cases p with
      | nil => simp [compactifyPairZ, compactify, evalZ, sub_eq_add_neg]
      | cons a p =>
          have hp := ih p
          have hB : evaluate [1,-1] x = 1-x := by simp [evaluate]; ring
          constructor
          · simp only [compactifyPairZ, evalZ_add, evalZ_scale, evalZ_linear, evalZ,
              Int.cast_one, Int.cast_neg, hp.1, hp.2, List.map_cons, compactify,
              evaluate_add, evaluate_scale, evaluate_mul, evaluate_power, hB,
              Rat.cast_intCast]
            simp only [evaluate_cons, evaluate_nil, Rat.cast_zero, Rat.cast_one,
              mul_zero, add_zero, mul_one, zero_add]
            rw [pow_succ]
            ring
          · simp only [compactifyPairZ, evalZ_linear, Int.cast_one, Int.cast_neg, hp.2]
            rw [pow_succ]
            ring

def compactifyZ (p : ZPoly) (n : ℕ) : ZPoly := (compactifyPairZ p n).1

theorem map_num_cast (p : Poly) (h : ∀ a ∈ p, a.den = 1) :
    (p.map Rat.num).map (fun (a : ℤ) => (a : ℚ)) = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      have ha := h a (by simp)
      have hp : ∀ b ∈ p, b.den = 1 := by intro b hb; exact h b (by simp [hb])
      simp only [List.map_cons, Rat.coe_int_num_of_den_eq_one ha, ih hp]

theorem compactifyZ_map_num_eval (p : Poly) (n : ℕ)
    (h : ∀ a ∈ p, a.den = 1) (x : ℝ) :
    evalZ (compactifyZ (p.map Rat.num) n) x = evaluate (compactify p n) x := by
  unfold compactifyZ
  rw [(evalZ_compactifyPair (p.map Rat.num) n x).1, map_num_cast p h]

def checkIntegerCompactified (p : Poly) (n : ℕ) (certificate : CompactCertificate) : Bool :=
  decide (p.length ≤ n+1) && p.all (fun a => a.den == 1) &&
    checkIntegerCompact (compactifyZ (p.map Rat.num) n) 0 1 certificate

theorem checkIntegerCompactified_implies
    (complete : ∀ p q : Poly, (∀ x : ℝ, evaluate p x = evaluate q x) → equal p q = true)
    (p : Poly) (n : ℕ) (certificate : CompactCertificate)
    (h : checkIntegerCompactified p n certificate = true) :
    checkCompactified p n certificate = true := by
  have hs := Bool.and_eq_true_iff.mp h
  have hg := Bool.and_eq_true_iff.mp hs.1
  have hp : ∀ a ∈ p, a.den = 1 := by
    intro a ha
    simpa using (List.all_eq_true.mp hg.2) a ha
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hg.1, ?_⟩
  exact checkIntegerCompact_transfer complete (compactifyZ (p.map Rat.num) n) (compactify p n)
    (compactifyZ_map_num_eval p n hp) 0 1 certificate hs.2

/-- Check an integer compactification. -/
def checkIntegerCompactifiedData (p : Poly) (n : ℕ) (certificate : CompactCertificate)
    (data : ZPoly) : Bool :=
  decide (p.length ≤ n+1) && p.all (fun a => a.den == 1) &&
    equalZ (compactifyZ (p.map Rat.num) n) data && checkIntegerCompact data 0 1 certificate

theorem checkIntegerCompactifiedData_implies
    (complete : ∀ p q : Poly, (∀ x : ℝ, evaluate p x = evaluate q x) → equal p q = true)
    (p : Poly) (n : ℕ) (certificate : CompactCertificate) (data : ZPoly)
    (h : checkIntegerCompactifiedData p n certificate data = true) :
    checkCompactified p n certificate = true := by
  have hs := Bool.and_eq_true_iff.mp h
  have he := Bool.and_eq_true_iff.mp hs.1
  have hg := Bool.and_eq_true_iff.mp he.1
  have hp : ∀ a ∈ p, a.den = 1 := by
    intro a ha
    simpa using (List.all_eq_true.mp hg.2) a ha
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hg.1, ?_⟩
  apply checkIntegerCompact_transfer complete data (compactify p n) ?_ 0 1 certificate hs.2
  intro x
  exact (equalZ_sound _ _ he.2 x).symm.trans (compactifyZ_map_num_eval p n hp x)

/-- Integer certificate soundness. -/
theorem accepted (p : Poly) (n : ℕ) (certificate : CompactCertificate)
    (h : checkIntegerCompactified p n certificate = true) :
    checkCompactified p n certificate = true :=
  checkIntegerCompactified_implies PositiveLeaf.equal_of_evaluate_eq p n certificate h

/-- Soundness of the integer compactification check. -/
theorem acceptedData (p : Poly) (n : ℕ) (certificate : CompactCertificate) (data : ZPoly)
    (h : checkIntegerCompactifiedData p n certificate data = true) :
    checkCompactified p n certificate = true :=
  checkIntegerCompactifiedData_implies PositiveLeaf.equal_of_evaluate_eq p n certificate data h

end R7.Core.Univariate.IntegerCompact
