import Mathlib.Data.Real.Basic

import R7.Spectral.Coordinates.Parameters
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators Matrix
namespace R7
abbrev Spectrum := Fin 6 → ℝ
abbrev BasisMatrix := Matrix (Fin 6) (Fin 5) ℝ

def Normalized (l : Spectrum) : Prop :=
  (∑ j, l j) = 0 ∧ (∑ j, (l j)^2) = 1

def IsTraceFreeOrthonormalBasis (R : BasisMatrix) : Prop :=
  R.transpose * R = 1 ∧ ∀ a, (∑ j, R j a) = 0

def moment (l : Spectrum) (n : ℕ) : ℝ := ∑ j, (l j)^n

def hEntry (l : Spectrum) (i j : Fin 6) : ℝ :=
  if j = i then 6*(l i)^2 - moment l 4
  else 4*(l i)^2 + 4*l i*l j + 10*(l j)^2 - 3*moment l 4

def hMatrix (l : Spectrum) (i : Fin 6) : Matrix (Fin 6) (Fin 6) ℝ := fun j k =>
  (if j = k then hEntry l i j else 0)
  - 4*((l j)^3*l k + l j*(l k)^3) + 4*moment l 4*l j*l k

def cMatrix (p : Parameters) (l : Spectrum) (i : Fin 6) (R : BasisMatrix) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  R.transpose * (show Matrix (Fin 6) (Fin 6) ℝ from fun j k =>
    (if j = k then ((p.m22:ℝ)-p.c6)*(if j=i then 1 else 3) else 0)
    - (p.m22:ℝ)*l j*l k - (p.c13:ℝ)*hMatrix l i j k) * R

def nVector (p : Parameters) (l : Spectrum) : Spectrum := fun j =>
  ((p.c3:ℝ)+(p.c14:ℝ)*moment l 4)*((l j)^2-1/6)
  + (p.c10:ℝ)*((l j)^4-moment l 4/6) + (p.c11:ℝ)*moment l 3*l j

def vVector (p : Parameters) (l : Spectrum) (i : Fin 6) : Spectrum := fun j =>
  ((p.c10:ℝ)+4*p.c12)*(l j)^3 + ((p.c10:ℝ)+3*p.c11)*l i*(l j)^2
  + ((p.c7:ℝ)+(p.c10:ℝ)*((l i)^2-2*(l i)^4)
      -2*(p.c11:ℝ)*moment l 3*l i-2*(p.c12:ℝ)*moment l 4)*l j
  + (p.c14:ℝ)*(moment l 4*l j+4*(l i)^2*(l j)^3-4*moment l 4*(l i)^2*l j)

def baseL (p : Parameters) (l : Spectrum) (i : Fin 6) (s : ℝ) : ℝ :=
  (2*(p.c3:ℝ)*(1-s/5)-1)*(l i)^2 - (p.c3:ℝ)*(1-2*s/5)
  - (3-s)*(s-2)/2*((p.c6:ℝ)+(p.c13:ℝ)*moment l 4)
  - (p.m22:ℝ)*(3-s)^2/4 - (p.c7:ℝ)*(s-2)/2
  + (p.c10:ℝ)*(2*(1-s/5)*(l i)^4-s*moment l 4/10)
  + 2*(p.c11:ℝ)*(1-s/5)*moment l 3*l i
  + (p.c12:ℝ)*(2-s)*moment l 4
  + (p.c14:ℝ)*moment l 4*(2*(1-s/5)*(l i)^2-s/10)

def inversePair (C : Matrix (Fin 5) (Fin 5) ℝ) (x z : Fin 5 → ℝ) : ℝ :=
  ∑ a, ∑ b, x a * C⁻¹ a b * z b

def projected (R : BasisMatrix) (x : Spectrum) : Fin 5 → ℝ :=
  fun a => ∑ j, R j a*x j

structure SchurData where
  T : ℝ
  U : ℝ
  J : ℝ
  E : ℝ
  z0 : ℝ
  z1 : ℝ
  z2 : ℝ

def schurData (p : Parameters) (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
    (s : ℝ) : SchurData :=
  let C := cMatrix p l i R
  let x := projected R l
  let v := projected R (vVector p l i)
  let T := inversePair C x x
  let U := inversePair C x v
  let J := inversePair C v v/4
  let W : ℝ := (p.c8:ℝ)-p.m12
  { T := T, U := U, J := J,
    E := 6/5-(p.m11:ℝ)-(p.m12:ℝ)^2*T,
    z0 := (p.c4:ℝ)+(p.m12:ℝ)*W*T,
    z1 := (p.c8:ℝ)-(p.m12:ℝ)*(3-s)+(p.m12:ℝ)*U,
    z2 := 6/5*nVector p l i }

def quarticCoefficients (p : Parameters) (l : Spectrum) (i : Fin 6)
    (R : BasisMatrix) (s : ℝ) : Fin 5 → ℝ :=
  let d := schurData p l i R s
  let W : ℝ := (p.c8:ℝ)-p.m12
  ![s*(5-2*s)/10-(p.m11:ℝ)/4-W^2*d.T/4-d.z0^2/(4*d.E),
    -(p.m12:ℝ)*(3-s)/2+(p.c8:ℝ)*(1-s/2)-W*d.U/2-d.z0*d.z1/(2*d.E),
    baseL p l i s+(p.m11:ℝ)-d.J-(d.z1^2+2*d.z0*d.z2)/(4*d.E),
    2*(p.m12:ℝ)-d.z1*d.z2/(2*d.E),
    (p.c6:ℝ)+(p.c13:ℝ)*moment l 4
      -((∑ j, (nVector p l j)^2)-6/5*(nVector p l i)^2)/4-d.z2^2/(4*d.E)]

def quartic (p : Parameters) (l : Spectrum) (i : Fin 6)
    (R : BasisMatrix) (s y : ℝ) : ℝ :=
  ∑ j : Fin 5, quarticCoefficients p l i R s j*y^(j.val)

end R7
