import R7.Spectral.Coordinates.Representation
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
namespace R7

@[simp] theorem moment_neg_three (l : Spectrum) :
    moment (fun j => -l j) 3 = -moment l 3 := by
  unfold moment
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem moment_neg_four (l : Spectrum) :
    moment (fun j => -l j) 4 = moment l 4 := by
  unfold moment
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem hEntry_neg (l : Spectrum) (i j : Fin 6) :
    hEntry (fun k => -l k) i j = hEntry l i j := by
  simp only [hEntry, moment_neg_four, even_two, Even.neg_pow, neg_mul, mul_neg, neg_neg]

@[simp] theorem hMatrix_neg (l : Spectrum) (i : Fin 6) :
    hMatrix (fun k => -l k) i = hMatrix l i := by
  ext j k
  simp only [hMatrix, moment_neg_four, hEntry_neg]
  ring

@[simp] theorem cMatrix_neg (p : Parameters) (l : Spectrum) (i : Fin 6) (R : BasisMatrix) :
    cMatrix p (fun j => -l j) i R = cMatrix p l i R := by
  unfold cMatrix
  congr 2
  funext j k
  simp

@[simp] theorem nVector_neg (p : Parameters) (l : Spectrum) :
    nVector p (fun j => -l j) = nVector p l := by
  funext j
  simp only [nVector, moment_neg_four, moment_neg_three]
  ring

@[simp] theorem vVector_neg (p : Parameters) (l : Spectrum) (i : Fin 6) :
    vVector p (fun j => -l j) i = fun j => -vVector p l i j := by
  funext j
  simp only [vVector, moment_neg_three, moment_neg_four]
  ring

@[simp] theorem baseL_neg (p : Parameters) (l : Spectrum) (i : Fin 6) (s : ℝ) :
    baseL p (fun j => -l j) i s = baseL p l i s := by
  simp only [baseL, moment_neg_three, moment_neg_four]
  ring

@[simp] theorem projected_neg (R : BasisMatrix) (x : Spectrum) :
    projected R (fun j => -x j) = fun a => -projected R x a := by
  funext a
  simp [projected, Finset.sum_neg_distrib]

@[simp] theorem inversePair_neg_neg (C : Matrix (Fin 5) (Fin 5) ℝ)
    (x z : Fin 5 → ℝ) :
    inversePair C (fun j => -x j) (fun j => -z j) = inversePair C x z := by
  simp [inversePair]

@[simp] theorem schurData_neg (p : Parameters) (l : Spectrum) (i : Fin 6)
    (R : BasisMatrix) (s : ℝ) :
    schurData p (fun j => -l j) i R s = schurData p l i R s := by
  simp [schurData]

@[simp] theorem quarticCoefficients_neg (p : Parameters) (l : Spectrum) (i : Fin 6)
    (R : BasisMatrix) (s : ℝ) :
    quarticCoefficients p (fun j => -l j) i R s = quarticCoefficients p l i R s := by
  simp [quarticCoefficients]

theorem quartic_neg (p : Parameters) (l : Spectrum) (i : Fin 6)
    (R : BasisMatrix) (s y : ℝ) :
    quartic p (fun j => -l j) i R s y = quartic p l i R s y := by
  simp [quartic]

def reindexSpectrum (e : Equiv.Perm (Fin 6)) (l : Spectrum) : Spectrum :=
  fun j => l (e j)
def reindexBasis (e : Equiv.Perm (Fin 6)) (R : BasisMatrix) : BasisMatrix :=
  fun j a => R (e j) a

@[simp] theorem moment_reindex (e : Equiv.Perm (Fin 6)) (l : Spectrum) (n : ℕ) :
    moment (reindexSpectrum e l) n = moment l n := by
  exact Equiv.sum_comp e (fun j => (l j)^n)

@[simp] theorem hEntry_reindex (e : Equiv.Perm (Fin 6)) (l : Spectrum) (i j : Fin 6) :
    hEntry (reindexSpectrum e l) i j = hEntry l (e i) (e j) := by
  simp [hEntry, reindexSpectrum, e.injective.eq_iff]

@[simp] theorem hMatrix_reindex (e : Equiv.Perm (Fin 6)) (l : Spectrum) (i j k : Fin 6) :
    hMatrix (reindexSpectrum e l) i j k = hMatrix l (e i) (e j) (e k) := by
  simp only [hMatrix, hEntry_reindex, moment_reindex, reindexSpectrum]
  simp only [e.injective.eq_iff]

private theorem gram_reindex (e : Equiv.Perm (Fin 6)) (R : BasisMatrix)
    (A : Matrix (Fin 6) (Fin 6) ℝ) :
    (reindexBasis e R).transpose * (show Matrix (Fin 6) (Fin 6) ℝ from fun j k => A (e j) (e k)) * reindexBasis e R
      = R.transpose * A * R := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reindexBasis]
  apply Fintype.sum_equiv e
  intro j
  congr 1
  exact Equiv.sum_comp e (fun k => R k a * A k (e j))

@[simp] theorem cMatrix_reindex (e : Equiv.Perm (Fin 6)) (p : Parameters)
    (l : Spectrum) (i : Fin 6) (R : BasisMatrix) :
    cMatrix p (reindexSpectrum e l) i (reindexBasis e R) = cMatrix p l (e i) R := by
  unfold cMatrix
  have h : (fun j k =>
      (if j = k then ((p.m22:ℝ)-p.c6)*(if j=i then 1 else 3) else 0)
      - (p.m22:ℝ)*reindexSpectrum e l j*reindexSpectrum e l k
      - (p.c13:ℝ)*hMatrix (reindexSpectrum e l) i j k)
    = (fun j k =>
      (if e j = e k then ((p.m22:ℝ)-p.c6)*(if e j=e i then 1 else 3) else 0)
      - (p.m22:ℝ)*l (e j)*l (e k) - (p.c13:ℝ)*hMatrix l (e i) (e j) (e k)) := by
    funext j k
    simp [reindexSpectrum]
  rw [h]
  exact gram_reindex e R (fun j k =>
    (if j = k then ((p.m22:ℝ)-p.c6)*(if j=e i then 1 else 3) else 0)
    - (p.m22:ℝ)*l j*l k - (p.c13:ℝ)*hMatrix l (e i) j k)

@[simp] theorem nVector_reindex (e : Equiv.Perm (Fin 6)) (p : Parameters) (l : Spectrum) :
    nVector p (reindexSpectrum e l) = reindexSpectrum e (nVector p l) := by
  funext j
  simp [nVector, reindexSpectrum]

@[simp] theorem vVector_reindex (e : Equiv.Perm (Fin 6)) (p : Parameters)
    (l : Spectrum) (i : Fin 6) :
    vVector p (reindexSpectrum e l) i = reindexSpectrum e (vVector p l (e i)) := by
  funext j
  simp [vVector, reindexSpectrum]

@[simp] theorem baseL_reindex (e : Equiv.Perm (Fin 6)) (p : Parameters)
    (l : Spectrum) (i : Fin 6) (s : ℝ) :
    baseL p (reindexSpectrum e l) i s = baseL p l (e i) s := by
  simp [baseL, reindexSpectrum]

@[simp] theorem projected_reindex (e : Equiv.Perm (Fin 6)) (R : BasisMatrix) (x : Spectrum) :
    projected (reindexBasis e R) (reindexSpectrum e x) = projected R x := by
  funext a
  exact Equiv.sum_comp e (fun j => R j a*x j)

@[simp] theorem schurData_reindex (e : Equiv.Perm (Fin 6)) (p : Parameters)
    (l : Spectrum) (i : Fin 6) (R : BasisMatrix) (s : ℝ) :
    schurData p (reindexSpectrum e l) i (reindexBasis e R) s = schurData p l (e i) R s := by
  simp [schurData, reindexSpectrum]

@[simp] theorem quarticCoefficients_reindex (e : Equiv.Perm (Fin 6)) (p : Parameters)
    (l : Spectrum) (i : Fin 6) (R : BasisMatrix) (s : ℝ) :
    quarticCoefficients p (reindexSpectrum e l) i (reindexBasis e R) s
      = quarticCoefficients p l (e i) R s := by
  have hsum : (∑ j, (nVector p l (e j))^2) = ∑ j, (nVector p l j)^2 :=
    Equiv.sum_comp e (fun j => (nVector p l j)^2)
  simp [quarticCoefficients, hsum, reindexSpectrum]

@[simp] theorem normalized_reindex (e : Equiv.Perm (Fin 6)) (l : Spectrum) :
    Normalized (reindexSpectrum e l) ↔ Normalized l := by
  have h1 := Equiv.sum_comp e l
  have h2 := Equiv.sum_comp e (fun j => (l j)^2)
  simp only [Normalized, reindexSpectrum, h1, h2]

@[simp] theorem basis_reindex (e : Equiv.Perm (Fin 6)) (R : BasisMatrix) :
    IsTraceFreeOrthonormalBasis (reindexBasis e R) ↔ IsTraceFreeOrthonormalBasis R := by
  have hgram : (reindexBasis e R).transpose * reindexBasis e R = R.transpose * R := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, reindexBasis]
    exact Equiv.sum_comp e (fun j => R j a*R j b)
  have hsum (a : Fin 5) : (∑ j, reindexBasis e R j a) = ∑ j, R j a :=
    Equiv.sum_comp e (fun j => R j a)
  simp only [IsTraceFreeOrthonormalBasis, hgram, hsum]

theorem quartic_signed_reindex_zero (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (e : Equiv.Perm (Fin 6)) (p : Parameters) (l : Spectrum) (i : Fin 6)
    (he : e 0 = i) (R : BasisMatrix) (s y : ℝ) :
    quartic p (fun j => ε*l (e j)) 0 (reindexBasis e R) s y = quartic p l i R s y := by
  have hre : quartic p (reindexSpectrum e l) 0 (reindexBasis e R) s y
      = quartic p l i R s y := by
    simp [quartic, he]
  rcases hε with rfl | rfl
  · simpa [reindexSpectrum] using hre
  · simpa only [neg_one_mul] using
      (quartic_neg p (reindexSpectrum e l) 0 (reindexBasis e R) s y).trans hre

end R7
