import R7.Spectral.CertificateCore
import R7.Algebra.UnivariateInteger
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Integer checks for slice-binding identities. -/
namespace R7.Core.SpectralCertificate.IntegerSlices
open R7.Core.Univariate R7.Core.Univariate.IntegerCompact
open R7.Core.MinorCertificates R7.Core.Bivariate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Multiplication uses integer coefficients throughout. -/
def mulZ : ZPoly → ZPoly → ZPoly
  | [], _ => []
  | a :: p, q => addZ (scaleZ a q) (0 :: mulZ p q)

def negZ (p : ZPoly) : ZPoly := p.map (- ·)
def subZ (p q : ZPoly) : ZPoly := addZ p (negZ q)
def squareZ (p : ZPoly) : ZPoly := mulZ p p

@[simp] theorem evalZ_mul (p q : ZPoly) (x : ℝ) :
    evalZ (mulZ p q) x = evalZ p x * evalZ q x := by
  induction p with
  | nil => simp [mulZ, evalZ]
  | cons a p ih => simp only [mulZ, evalZ_add, evalZ_scale, evalZ, Int.cast_zero, ih]; ring

@[simp] theorem evalZ_neg (p : ZPoly) (x : ℝ) :
    evalZ (negZ p) x = -evalZ p x := by
  induction p with
  | nil => simp [negZ, evalZ]
  | cons a p ih => simp only [negZ, List.map_cons, evalZ, Int.cast_neg] at *; rw [ih]; ring

@[simp] theorem evalZ_sub (p q : ZPoly) (x : ℝ) :
    evalZ (subZ p q) x = evalZ p x - evalZ q x := by simp [subZ, sub_eq_add_neg]

@[simp] theorem evalZ_square (p : ZPoly) (x : ℝ) :
    evalZ (squareZ p) x = (evalZ p x)^2 := by simp [squareZ, pow_two]

def integralPoly (p : Poly) : Bool := p.all (fun q => q.den == 1)
def integralBiPoly (p : BiPoly) : Bool := p.all integralPoly

theorem integralPoly_sound (p : Poly) (h : integralPoly p = true) :
    ∀ q ∈ p, q.den = 1 := by
  intro q hq
  have hh := (List.all_eq_true.mp h) q hq
  simpa using hh

theorem integral_coefficient (p : BiPoly) (h : integralBiPoly p = true) (k : ℕ) :
    integralPoly (coefficient p k) = true := by
  cases he : p[k]? with
  | none => simp [coefficient, he, integralPoly]
  | some row =>
      have hr := (List.all_eq_true.mp h) row (List.mem_of_getElem? he)
      simpa [coefficient, he] using hr

def coefficientZ (p : BiPoly) (k : ℕ) : ZPoly := (coefficient p k).map Rat.num

@[simp] theorem evalZ_coefficient (p : BiPoly) (h : integralBiPoly p = true)
    (k : ℕ) (x : ℝ) :
    evalZ (coefficientZ p k) x = evaluate (coefficient p k) x :=
  evalZ_map_num _ (integralPoly_sound _ (integral_coefficient p h k)) x

def diagonalZ (p : BiPoly) : ℕ → ZPoly
  | 0 => scaleZ 100 (coefficientZ p 0)
  | 1 => scaleZ 98 (coefficientZ p 2)
  | j+2 => scaleZ 100 (coefficientZ p (2*(j+2)))

def offZ (p : BiPoly) (j : ℕ) : ZPoly := scaleZ 50 (coefficientZ p (2*j+1))

/-- Seven corrected minors, with each predecessor computed once. -/
def cachedBandZ (p : BiPoly) : Fin 7 → ZPoly :=
  let d0 := diagonalZ p 0
  let d1 := diagonalZ p 1
  let d2 := diagonalZ p 2
  let o0 := offZ p 0
  let o1 := offZ p 1
  let c := coefficientZ p 2
  let m1 := d0
  let m2 := subZ (mulZ d0 d1) (squareZ o0)
  let m3 := subZ (subZ (subZ
    (addZ (mulZ (mulZ d0 d1) d2) (scaleZ 2 (mulZ (mulZ o0 o1) c)))
    (mulZ d0 (squareZ o1))) (mulZ d1 (squareZ c))) (mulZ d2 (squareZ o0))
  let m4 := subZ (mulZ (diagonalZ p 3) m3) (mulZ (squareZ (offZ p 2)) m2)
  let m5 := subZ (mulZ (diagonalZ p 4) m4) (mulZ (squareZ (offZ p 3)) m3)
  let m6 := subZ (mulZ (diagonalZ p 5) m5) (mulZ (squareZ (offZ p 4)) m4)
  let m7 := subZ (mulZ (diagonalZ p 6) m6) (mulZ (squareZ (offZ p 5)) m5)
  ![m1,m2,m3,m4,m5,m6,m7]

/-- Five ordinary tridiagonal minors. -/
def cachedOrdinaryZ (p : BiPoly) : Fin 5 → ZPoly :=
  let d (j : ℕ) := scaleZ 2 (coefficientZ p (2*j))
  let o (j : ℕ) := coefficientZ p (2*j+1)
  let m0 : ZPoly := [1]
  let m1 := d 0
  let m2 := subZ (mulZ (d 1) m1) (mulZ (squareZ (o 0)) m0)
  let m3 := subZ (mulZ (d 2) m2) (mulZ (squareZ (o 1)) m1)
  let m4 := subZ (mulZ (d 3) m3) (mulZ (squareZ (o 2)) m2)
  let m5 := subZ (mulZ (d 4) m4) (mulZ (squareZ (o 3)) m3)
  ![m1,m2,m3,m4,m5]

theorem cachedBandZ_eval (p : BiPoly) (h : integralBiPoly p = true)
    (j : Fin 7) (x : ℝ) :
    evalZ (cachedBandZ p j) x = evaluate (bandMinor p (j.val+1)) x := by
  have hc (k : ℕ) := evalZ_coefficient p h k x
  fin_cases j <;>
    simp [cachedBandZ, diagonalZ, offZ, bandMinor, diagonal, off, minus, hc] <;> ring

theorem cachedOrdinaryZ_eval (p : BiPoly) (h : integralBiPoly p = true)
    (j : Fin 5) (x : ℝ) :
    evalZ (cachedOrdinaryZ p j) x = evaluate (minorPolynomial p (j.val+1)) x := by
  have hc (k : ℕ) := evalZ_coefficient p h k x
  fin_cases j <;>
    simp [cachedOrdinaryZ, minorPolynomial, hc, evalZ] <;> ring

/-- Check integer representability and equality of the witness. -/
def checkWitness (q : ZPoly) (w : MinorWitness) : Bool :=
  integralPoly w.polynomial && (w.scale.den == 1) &&
    equalZ q (scaleZ w.scale.num (w.polynomial.map Rat.num))

theorem checkWitness_sound (q : ZPoly) (w : MinorWitness)
    (h : checkWitness q w = true) (x : ℝ) :
    evalZ q x = evaluate (Univariate.scale w.scale w.polynomial) x := by
  have hs := Bool.and_eq_true_iff.mp h
  have hg := Bool.and_eq_true_iff.mp hs.1
  have hd : w.scale.den = 1 := by simpa using hg.2
  have hi := integralPoly_sound w.polynomial hg.1
  have he := equalZ_sound q (scaleZ w.scale.num (w.polynomial.map Rat.num)) hs.2 x
  rw [evalZ_scale, evalZ_map_num _ hi, cast_num_eq _ hd] at he
  simpa only [evaluate_scale] using he

def checkBand (p : BiPoly) (w : Fin 7 → MinorWitness) : Bool :=
  integralBiPoly p && (List.finRange 7).all (fun j => checkWitness (cachedBandZ p j) (w j))

def checkOrdinary (p : BiPoly) (w : Fin 5 → MinorWitness) : Bool :=
  integralBiPoly p && (List.finRange 5).all (fun j => checkWitness (cachedOrdinaryZ p j) (w j))

/-- Soundness of the corrected binding check. -/
theorem band_accepted (p : BiPoly) (w : Fin 7 → MinorWitness)
    (h : checkBand p w = true) : minorBindings p w := by
  have hs := Bool.and_eq_true_iff.mp h
  intro j
  apply PositiveLeaf.equal_of_evaluate_eq
  intro x
  have hj := (List.all_eq_true.mp hs.2) j (List.mem_finRange j)
  rw [← cachedBandZ_eval p hs.1 j x]
  exact checkWitness_sound _ _ hj x

/-- Soundness of the binding check. -/
theorem ordinary_accepted (p : BiPoly) (w : Fin 5 → MinorWitness)
    (h : checkOrdinary p w = true) : ordinaryBindings p w := by
  have hs := Bool.and_eq_true_iff.mp h
  intro j
  apply PositiveLeaf.equal_of_evaluate_eq
  intro x
  have hj := (List.all_eq_true.mp hs.2) j (List.mem_finRange j)
  rw [← cachedOrdinaryZ_eval p hs.1 j x]
  exact checkWitness_sound _ _ hj x

end R7.Core.SpectralCertificate.IntegerSlices
