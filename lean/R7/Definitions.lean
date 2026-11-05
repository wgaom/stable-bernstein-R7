import R7.Scalar.Parameters
import Mathlib.Data.Real.Sqrt

/-! Parameters and definitions used in Appendix A of R7.tex.
The rows below are Table A.1; Lean indices start at zero. -/

noncomputable section
namespace R7.Paper
open scoped BigOperators

abbrev Parameters := R7.Core.Parameters

def rows (r : Fin 11) : Parameters :=
 match r.val with
 | 0 => { sigmaL := 2.46, sigmaR := 2.4845, c3 := 1.323, c4 := 0.0304, c6 := 0.249, c7 := -0.518, c8 := -0.0339, m11 := 0.0282, m22 := 1.667, m12 := 0.0097 }
 | 1 => { sigmaL := 2.4845, sigmaR := 2.4895, c3 := 1.606, c4 := 0.0196, c6 := 0.344, c7 := -1.22, c8 := -0.0229, m11 := 0.0199, m22 := 3.335, m12 := 0.0075 }
 | 2 => { sigmaL := 2.4895, sigmaR := 2.492, c3 := 1.708, c4 := 0.0154, c6 := 0.389, c7 := -1.485, c8 := -0.0199, m11 := 0.0155, m22 := 4.046, m12 := 0.005 }
 | 3 => { sigmaL := 2.492, sigmaR := 2.4933, c3 := 1.762, c4 := 0.0131, c6 := 0.414, c7 := -1.628, c8 := -0.0186, m11 := 0.013, m22 := 4.441, m12 := 0.0034 }
 | 4 => { sigmaL := 2.4933, sigmaR := 2.4941, c3 := 1.793, c4 := 0.0104, c6 := 0.429, c7 := -1.717, c8 := -0.0184, m11 := 0.0115, m22 := 4.693, m12 := 0.0023 }
 | 5 => { sigmaL := 2.4941, sigmaR := 2.4947, c3 := 1.816, c4 := 0.01, c6 := 0.44, c7 := -1.783, c8 := -0.0182, m11 := 0.0104, m22 := 4.884, m12 := 0.0014 }
 | 6 => { sigmaL := 2.4947, sigmaR := 2.4951, c3 := 1.837, c4 := 0.0092, c6 := 0.45, c7 := -1.835, c8 := -0.0178, m11 := 0.0096, m22 := 5.026, m12 := 0.0007 }
 | 7 => { sigmaL := 2.4951, sigmaR := 2.4954, c3 := 1.841, c4 := 0.0091, c6 := 0.452, c7 := -1.864, c8 := -0.017, m11 := 0.009, m22 := 5.119, m12 := 0.0002 }
 | 8 => { sigmaL := 2.4954, sigmaR := 2.4957, c3 := 1.857, c4 := 0.0078, c6 := 0.46, c7 := -1.896, c8 := -0.0169, m11 := 0.0084, m22 := 5.202, m12 := 0 }
 | 9 => { sigmaL := 2.4957, sigmaR := 2.496, c3 := 1.861, c4 := 0.0065, c6 := 0.462, c7 := -1.921, c8 := -0.0157, m11 := 0.0079, m22 := 5.276, m12 := 0 }
 | _ => { sigmaL := 2.496, sigmaR := 2.4962, c3 := 1.873, c4 := 0.0068, c6 := 0.468, c7 := -1.939, c8 := -0.016, m11 := 0.0074, m22 := 5.325, m12 := 0 }

def endpoint (r : Fin 11) (side : Fin 2) : ℝ :=
 if side.val=0 then (rows r).sigmaL else (rows r).sigmaR

def detM (p : Parameters) : ℝ := p.m22*p.m11-p.m12^2
def beta (p : Parameters) (ρ : ℝ) : ℝ :=
  detM p / ((p.m11 : ℝ)+2*p.m12*Real.sqrt ρ+p.m22*ρ)

def m11tilde (p : Parameters) (ρ : ℝ) : ℝ := p.m11-ρ*beta p ρ
def m12tilde (p : Parameters) (ρ : ℝ) : ℝ := p.m12+Real.sqrt ρ*beta p ρ

def alpha (p : Parameters) (q ρ : ℝ) : ℝ :=
  ((p.m22 : ℝ)-p.c6)/(1/3+q^2/2)-p.m22+beta p ρ

def eta (p : Parameters) (q ρ : ℝ) : ℝ :=
  6/5-m11tilde p ρ-(m12tilde p ρ)^2/alpha p q ρ

def B0 (p : Parameters) (σ u ρ : ℝ) : ℝ :=
  σ*(5-2*σ)/10-(p.m11 : ℝ)/4+(p.c6 : ℝ)*ρ^2+2*p.m12*ρ*Real.sqrt ρ+
  ((p.c8 : ℝ)*(1-σ/2)-(p.m12 : ℝ)*(3-σ)/2)*Real.sqrt ρ+
  ρ*beta p ρ*(1-σ/2)^2+
  ρ*((2*(p.c3 : ℝ)*(1-σ/5)-1)*u-(p.c3 : ℝ)*(1-2*σ/5)+p.m11-
    (p.c6 : ℝ)/2*(3-σ)*(σ-2)-(p.m22 : ℝ)/4*(3-σ)^2-
    (p.c7 : ℝ)/2*(σ-2))

def B1 (p : Parameters) (σ ρ : ℝ) : ℝ :=
  (p.c7 : ℝ)*Real.sqrt ρ+p.c8-p.m12+2*Real.sqrt ρ*beta p ρ*(1-σ/2)

def B2 (p : Parameters) (σ ρ : ℝ) : ℝ :=
  p.c4+((p.c8 : ℝ)-(p.m12 : ℝ)*(3-σ))*Real.sqrt ρ-2*ρ*beta p ρ*(1-σ/2)

def Lambda (q : ℝ) : ℝ :=
 207/125*q^4-33/25*q^2+29/60+6/125*q*(Real.sqrt (5-6*q^2))^3

def scalarF (p : Parameters) (σ q ρ : ℝ) : ℝ :=
  B0 p σ (q^2) ρ-(B1 p σ ρ)^2/(4*alpha p q ρ)
  -(p.c3 : ℝ)^2/4*(Lambda q-6/5*(q^2-1/6)^2)*ρ^2
  -(6/5*(p.c3 : ℝ)*(q^2-1/6)*ρ+B2 p σ ρ+
    m12tilde p ρ*B1 p σ ρ/alpha p q ρ)^2/(4*eta p q ρ)

def s (l : Fin 6 → ℝ) (k : ℕ) : ℝ := ∑ j, (l j)^k
def c3 : ℝ := 2.67
def c5 : ℝ := 6.04
def c6 : ℝ := 0.52
def c7 : ℝ := -4.18
def c10 : ℝ := -1.25
def c11 : ℝ := 0.37
def c12 : ℝ := 1.98

def N (l : Fin 6 → ℝ) (j : Fin 6) : ℝ :=
 c3*(l j)^2+c10*(l j)^4+c11*s l 3*l j-(c3+c10*s l 4)/6

def V (l : Fin 6 → ℝ) (i j : Fin 6) : ℝ :=
 (c10+4*c12)*(l j)^3+(c10+3*c11)*l i*(l j)^2+
 (c7+c10*((l i)^2-2*(l i)^4)-2*c11*s l 3*l i-2*c12*s l 4)*l j

def minimum (l : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
 sInf {e : ℝ | ∃ z : Fin 6 → ℝ, (∑ j, z j)=0 ∧
   e=(c5-c6)*(z i^2+3*(∑ j ∈ Finset.univ.erase i, z j^2))
     -c5*(∑ j, l j*z j)^2+∑ j, V l i j*z j}

def L (l : Fin 6 → ℝ) (i : Fin 6) (σ : ℝ) : ℝ :=
 2*(1-σ/5)*N l i-(l i)^2-c5/4*(3-σ)^2+
 (σ-2)*(c3/3-c7/2-c6/2*(3-σ)-(c10/6+c12)*s l 4)+minimum l i

def Q (l : Fin 6 → ℝ) : ℝ := c6-(∑ j, (N l j)^2)/4

def spectralF (l : Fin 6 → ℝ) (i : Fin 6) (σ ρ : ℝ) : ℝ :=
 σ*(5-2*σ)/10+L l i σ*ρ+Q l*ρ^2

end R7.Paper
