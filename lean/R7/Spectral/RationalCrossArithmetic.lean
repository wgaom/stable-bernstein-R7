import R7.Spectral.PolynomialCompute

/-! Sparse rational arithmetic checked by integer cross multiplication.
Sound for arbitrary lists; noncanonical representations may be rejected. -/

namespace R7.Core.SpectralCoefficient

private theorem mul_den (q : ℚ) : q * (q.den : ℚ) = (q.num : ℚ) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt q.den_pos)
  exact ((div_eq_iff hd).mp (Rat.num_div_den q)).symm

private theorem den_ne_zero (q : ℚ) : (q.den : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt q.den_pos)

namespace RationalCrossAdd

/-- Numerator of the unreduced sum over the product denominator. -/
def sumNumerator (a b : ℚ) : ℤ :=
  a.num * (b.den : ℤ) + b.num * (a.den : ℤ)

def sumCrossEqual (a b c : ℚ) : Bool :=
  sumNumerator a b * (c.den : ℤ) == c.num * (a.den : ℤ) * (b.den : ℤ)

theorem sumNumerator_spec (a b : ℚ) :
    (sumNumerator a b : ℚ) = (a + b) * ((a.den : ℚ) * (b.den : ℚ)) := by
  simp only [sumNumerator, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [← mul_den a, ← mul_den b]
  ring

theorem sumNumerator_zero_sound (a b : ℚ)
    (h : (sumNumerator a b == 0) = true) : a + b = 0 := by
  have hi : sumNumerator a b = 0 := by simpa using h
  have hc := congrArg (fun z : ℤ => (z : ℚ)) hi
  simp only [Int.cast_zero, sumNumerator_spec] at hc
  exact (mul_eq_zero.mp hc).resolve_right (mul_ne_zero (den_ne_zero a) (den_ne_zero b))

theorem sumCrossEqual_sound (a b c : ℚ) (h : sumCrossEqual a b c = true) :
    a + b = c := by
  have hi : sumNumerator a b * (c.den : ℤ) = c.num * (a.den : ℤ) * (b.den : ℤ) := by
    simpa only [sumCrossEqual, beq_iff_eq] using h
  have hc := congrArg (fun z : ℤ => (z : ℚ)) hi
  simp only [Int.cast_mul, Int.cast_natCast] at hc
  have hd := mul_ne_zero (mul_ne_zero (den_ne_zero a) (den_ne_zero b)) (den_ne_zero c)
  apply mul_right_cancel₀ hd
  calc
    (a + b) * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) =
        (sumNumerator a b : ℚ) * (c.den : ℚ) := by rw [sumNumerator_spec]; ring
    _ = (c.num : ℚ) * (a.den : ℚ) * (b.den : ℚ) := hc
    _ = c * ((a.den : ℚ) * (b.den : ℚ) * (c.den : ℚ)) := by rw [← mul_den c]; ring

def sameMonomial (a b : Term) : Bool :=
  (a.key == b.key) && expEqual a.exp b.exp

theorem sameMonomial_sound (a b : Term) (h : sameMonomial a b = true) : a.exp = b.exp := by
  exact (expEqual_eq_true _ _).mp (Bool.and_eq_true_iff.mp h).2

/-- Fuel exhaustion rejects, rather than accepting an unchecked fallback.
A canonical input pair with fewer than 65536 merge steps fits the public
wrapper below; soundness holds for every fuel and arbitrary term lists. -/
def check : ℕ → KeyPoly → KeyPoly → KeyPoly → Bool
  | 0, _, _, _ => false
  | _ + 1, [], q, r => keyPolyEqual q r
  | _ + 1, p, [], r => keyPolyEqual p r
  | n + 1, a :: p, b :: q, r =>
    bif sameMonomial a b then
      bif sumNumerator a.value b.value == 0 then check n p q r
      else match r with
        | [] => false
        | c :: r => sameMonomial a c &&
            (sumCrossEqual a.value b.value c.value && check n p q r)
    else bif Nat.ble a.key b.key then
      match r with
      | [] => false
      | c :: r => termEqual a c && check n p (b :: q) r
    else
      match r with
      | [] => false
      | c :: r => termEqual b c && check n (a :: p) q r

theorem check_cons (n : ℕ) (a b : Term) (p q r : KeyPoly) :
    check (n + 1) (a :: p) (b :: q) r =
    (bif sameMonomial a b then
      bif sumNumerator a.value b.value == 0 then check n p q r
      else match r with
        | [] => false
        | c :: r => sameMonomial a c &&
            (sumCrossEqual a.value b.value c.value && check n p q r)
    else bif Nat.ble a.key b.key then
      match r with
      | [] => false
      | c :: r => termEqual a c && check n p (b :: q) r
    else
      match r with
      | [] => false
      | c :: r => termEqual b c && check n (a :: p) q r) := rfl

theorem check_sound (n : ℕ) (p q r : KeyPoly) (h : check n p q r = true) :
    interpretKey r = interpretKey p + interpretKey q := by
  induction n generalizing p q r with
  | zero => simp [check] at h
  | succ n ih =>
    cases p with
    | nil =>
      change keyPolyEqual q r = true at h
      have he := keyPolyEqual_sound q r h
      subst r
      simp [interpretKey]
    | cons a p =>
      cases q with
      | nil =>
        change keyPolyEqual (a :: p) r = true at h
        have he := keyPolyEqual_sound (a :: p) r h
        subst r
        simp [interpretKey]
      | cons b q =>
        by_cases hab : sameMonomial a b = true
        · have heab := sameMonomial_sound a b hab
          by_cases hz : (sumNumerator a.value b.value == 0) = true
          · have hh : check n p q r = true := by
              simpa only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hz, ite_true] using h
            have hi := ih p q r hh
            have hv := sumNumerator_zero_sound a.value b.value hz
            have hm : MvPolynomial.monomial (R7.ComputablePolynomial.exponent a.exp) a.value +
                MvPolynomial.monomial (R7.ComputablePolynomial.exponent b.exp) b.value = 0 := by
              rw [← heab, ← map_add, hv, map_zero]
            rw [hi]
            simp only [interpretKey]
            linear_combination -hm
          · cases r with
            | nil =>
              simp only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hz, ite_true, ite_false] at h
            | cons c r =>
              have hh : sameMonomial a c = true ∧
                  (sumCrossEqual a.value b.value c.value = true ∧ check n p q r = true) := by
                simpa only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hz, ite_true, ite_false,
                  Bool.and_eq_true_iff] using h
              have heac := sameMonomial_sound a c hh.1
              have hv := sumCrossEqual_sound a.value b.value c.value hh.2.1
              have hm : MvPolynomial.monomial (R7.ComputablePolynomial.exponent c.exp) c.value =
                  MvPolynomial.monomial (R7.ComputablePolynomial.exponent a.exp) a.value +
                    MvPolynomial.monomial (R7.ComputablePolynomial.exponent b.exp) b.value := by
                rw [← heac, ← hv, map_add, heab]
              simp only [interpretKey]
              rw [hm, ih p q r hh.2.2]
              abel
        · by_cases hk : Nat.ble a.key b.key = true
          · cases r with
            | nil =>
              simp only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hk, ite_false, ite_true] at h
            | cons c r =>
              have hh : termEqual a c = true ∧ check n p (b :: q) r = true := by
                simpa only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hk, ite_false, ite_true,
                  Bool.and_eq_true_iff] using h
              have he := termEqual_sound a c hh.1
              subst c
              have hi := ih p (b :: q) r hh.2
              simp only [interpretKey] at hi ⊢
              rw [hi]
              abel
          · cases r with
            | nil =>
              simp only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hk, ite_false] at h
            | cons c r =>
              have hh : termEqual b c = true ∧ check n (a :: p) q r = true := by
                simpa only [check_cons, cond_eq_ite, Bool.false_eq_true, hab, hk, ite_false,
                  Bool.and_eq_true_iff] using h
              have he := termEqual_sound b c hh.1
              subst c
              have hi := ih (a :: p) q r hh.2
              simp only [interpretKey] at hi ⊢
              rw [hi]
              abel

def verifyAdd (p q r : KeyPoly) : Bool := check 65536 p q r

theorem verifyAdd_sound (p q r : KeyPoly) (h : verifyAdd p q r = true) :
    interpretKey r = interpretKey p + interpretKey q := check_sound 65536 p q r h

end RationalCrossAdd

/-! Scalar multiplication checked by integer cross multiplication. -/
namespace RationalCrossScale

def productCrossEqual (c a b : ℚ) : Bool :=
  c.num * a.num * (b.den : ℤ) == b.num * (c.den : ℤ) * (a.den : ℤ)

theorem productCrossEqual_sound (c a b : ℚ) (h : productCrossEqual c a b = true) :
    c * a = b := by
  have hi : c.num * a.num * (b.den : ℤ) = b.num * (c.den : ℤ) * (a.den : ℤ) := by
    simpa only [productCrossEqual, beq_iff_eq] using h
  have hc := congrArg (fun z : ℤ => (z : ℚ)) hi
  simp only [Int.cast_mul, Int.cast_natCast] at hc
  have hd := mul_ne_zero (mul_ne_zero (den_ne_zero c) (den_ne_zero a)) (den_ne_zero b)
  apply mul_right_cancel₀ hd
  calc
    (c * a) * ((c.den : ℚ) * (a.den : ℚ) * (b.den : ℚ)) =
        (c.num : ℚ) * (a.num : ℚ) * (b.den : ℚ) := by
          rw [← mul_den c, ← mul_den a]
          ring
    _ = (b.num : ℚ) * (c.den : ℚ) * (a.den : ℚ) := hc
    _ = b * ((c.den : ℚ) * (a.den : ℚ) * (b.den : ℚ)) := by
      rw [← mul_den b]
      ring

def check (c : ℚ) : KeyPoly → KeyPoly → Bool
  | [], [] => true
  | a :: p, b :: r => RationalCrossAdd.sameMonomial a b &&
      (productCrossEqual c a.value b.value && check c p r)
  | _, _ => false

theorem check_sound (c : ℚ) (p r : KeyPoly) (h : check c p r = true) :
    interpretKey r = MvPolynomial.C c * interpretKey p := by
  induction p generalizing r with
  | nil =>
    cases r with
    | nil => simp [interpretKey]
    | cons b r => simp [check] at h
  | cons a p ih =>
    cases r with
    | nil => simp [check] at h
    | cons b r =>
      have hh : RationalCrossAdd.sameMonomial a b = true ∧
          (productCrossEqual c a.value b.value = true ∧ check c p r = true) := by
        simpa only [check, Bool.and_eq_true_iff] using h
      have he := RationalCrossAdd.sameMonomial_sound a b hh.1
      have hv := productCrossEqual_sound c a.value b.value hh.2.1
      have hm : MvPolynomial.monomial (R7.ComputablePolynomial.exponent b.exp) b.value =
          MvPolynomial.C c * MvPolynomial.monomial (R7.ComputablePolynomial.exponent a.exp) a.value := by
        rw [← he, ← hv, MvPolynomial.C_mul_monomial]
      simp only [interpretKey]
      rw [hm, ih r hh.2.2, mul_add]

def verifyScale (scalar p r : KeyPoly) : Bool :=
  match scalar with
  | [a] => expEqual a.exp 0 && check a.value p r
  | _ => false

theorem verifyScale_sound (scalar p r : KeyPoly) (h : verifyScale scalar p r = true) :
    interpretKey r = interpretKey scalar * interpretKey p := by
  cases scalar with
  | nil => simp [verifyScale] at h
  | cons a scalar =>
    cases scalar with
    | cons b scalar => simp [verifyScale] at h
    | nil =>
      have hh : expEqual a.exp 0 = true ∧ check a.value p r = true := by
        simpa only [verifyScale, Bool.and_eq_true_iff] using h
      have he := (expEqual_eq_true _ _).mp hh.1
      simpa [interpretKey, he] using check_sound a.value p r hh.2

end RationalCrossScale

end R7.Core.SpectralCoefficient
