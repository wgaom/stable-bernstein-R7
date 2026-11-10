import R7.Algebra.ComputablePolynomial
import R7.Spectral.Coordinates.PolynomialChart
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.RCLike.Basic

namespace R7.Core.SpectralPolynomial
open scoped BigOperators
open R7.ComputablePolynomial

namespace Expr

def eval (x : Fin 5 → ℝ) : Expr → ℝ
 | .rat a => (a:ℝ)
 | .var i => x i
 | .add a b => eval x a + eval x b
 | .neg a => -eval x a
 | .mul a b => eval x a * eval x b
 | .pow a n => eval x a ^ n

@[simp] theorem eval_denote (x : Fin 5 → ℝ) (a : Expr) :
    MvPolynomial.aeval x a.denote = eval x a := by
  induction a <;> simp_all [ComputablePolynomial.Expr.denote, eval]

end Expr

private def esum6 (f : Fin 6 → Expr) : Expr :=
 .add (f 0) (.add (f 1) (.add (f 2) (.add (f 3) (.add (f 4) (f 5)))))

@[simp] private theorem eval_esum6 (x : Fin 5 → ℝ) (f : Fin 6 → Expr) :
    Expr.eval x (esum6 f) = ∑ j, Expr.eval x (f j) := by
  simp [esum6, Expr.eval, Fin.sum_univ_succ]

local instance : Add Expr := ⟨Expr.add⟩
local instance : Sub Expr := ⟨fun a b => Expr.add a (Expr.neg b)⟩
local instance : Mul Expr := ⟨Expr.mul⟩
local instance : Neg Expr := ⟨Expr.neg⟩
local instance (n : ℕ) : OfNat Expr n := ⟨Expr.rat n⟩
local instance : Pow Expr ℕ := ⟨Expr.pow⟩

private def rat := Expr.rat

def kappa : Fin 6 → Expr :=
 let z := Expr.var 0
 let g : Fin 4 → Expr := fun a => Expr.var a.succ
 ![5*z, -z-4*g 0-3*g 1-2*g 2-g 3,
   -z+g 0-3*g 1-2*g 2-g 3,
   -z+g 0+2*g 1-2*g 2-g 3,
   -z+g 0+2*g 1+3*g 2-g 3,
   -z+g 0+2*g 1+3*g 2+4*g 3]

def thetaE := esum6 (fun j => kappa j ^ 2)
def thirdE := esum6 (fun j => kappa j ^ 3)
def fourthE := esum6 (fun j => kappa j ^ 4)

def nE (j : Fin 6) : Expr :=
 rat (267/100) * kappa j^2*thetaE + rat (-5/4)*kappa j^4
  +rat (37/100)*thirdE*kappa j
  -(rat (267/100)*thetaE^2+rat (-5/4)*fourthE)*rat (1/6)

def vE (j : Fin 6) : Expr :=
 rat ((-5/4)+4*(99/50))*kappa j^3*thetaE
 +rat ((-5/4)+3*(37/100))*kappa 0*kappa j^2*thetaE
 +(rat (-209/50)*thetaE^2+rat (-5/4)*(kappa 0^2*thetaE-2*kappa 0^4)
   -rat (2*(37/100))*thirdE*kappa 0-rat (2*(99/50))*fourthE)*kappa j

def baseE (σ : ℚ) : Expr :=
 rat (2*(267/100)*(1-σ/5)-1)*kappa 0^2*thetaE
 +rat (-(267/100)*(1-2*σ/5)-(13/25)*(3-σ)*(σ-2)/2
   -(151/25)*(3-σ)^2/4-(-209/50)*(σ-2)/2)*thetaE^2
 +rat (-5/4)*(rat (2*(1-σ/5))*kappa 0^4-rat (σ/10)*fourthE)
 +rat (2*(37/100)*(1-σ/5))*thirdE*kappa 0
 +rat ((99/50)*(2-σ))*fourthE

def weight (j : Fin 6) : ℚ := if j=0 then 1 else 1/3

def covE (u v : Fin 6 → Expr) : Expr :=
 esum6 (fun j => rat (weight j)*u j*v j)
 -rat (3/8)*esum6 (fun j => rat (weight j)*u j)*esum6 (fun j => rat (weight j)*v j)

def dE : Expr := rat (2*(151/25)/3-13/25)*thetaE-rat ((151/25)/2)*kappa 0^2

def denominatorE : Expr := rat (4*((151/25)-(13/25)))*dE*thetaE^5

def constantE (σ a₀ : ℚ) : Expr := rat (σ*(5-2*σ)/10-a₀)*denominatorE

def linearE (σ : ℚ) : Expr :=
 rat (4*((151/25)-(13/25)))*dE*thetaE^3*baseE σ
 -dE*covE vE vE-rat (151/25)*(covE vE kappa)^2
 -rat (1/100000000)*denominatorE

def quarticE : Expr :=
 rat ((13/25)-1/100000000)*thetaE^4
 -rat (1/4)*esum6 (fun j => nE j^2)

def quadraticE : Expr := rat (4*((151/25)-(13/25)))*dE*thetaE*quarticE

noncomputable section

def theta (κ : Fin 6 → ℝ) : ℝ := ∑ j, κ j^2
def third (κ : Fin 6 → ℝ) : ℝ := ∑ j, κ j^3
def fourth (κ : Fin 6 → ℝ) : ℝ := ∑ j, κ j^4

def nHom (κ : Fin 6 → ℝ) (j : Fin 6) : ℝ :=
 (267/100)*κ j^2*theta κ +(-5/4)*κ j^4+(37/100)*third κ*κ j
 -((267/100)*theta κ^2+(-5/4)*fourth κ)/6

def vHom (κ : Fin 6 → ℝ) (j : Fin 6) : ℝ :=
 ((-5/4)+4*(99/50))*κ j^3*theta κ
 +((-5/4)+3*(37/100))*κ 0*κ j^2*theta κ
 +((-209/50)*theta κ^2+(-5/4)*(κ 0^2*theta κ-2*κ 0^4)
   -2*(37/100)*third κ*κ 0-2*(99/50)*fourth κ)*κ j

def baseHom (σ : ℝ) (κ : Fin 6 → ℝ) : ℝ :=
 (2*(267/100)*(1-σ/5)-1)*κ 0^2*theta κ
 +(-(267/100)*(1-2*σ/5)-(13/25)*(3-σ)*(σ-2)/2
   -(151/25)*(3-σ)^2/4-(-209/50)*(σ-2)/2)*theta κ^2
 +(-5/4)*(2*(1-σ/5)*κ 0^4-(σ/10)*fourth κ)
 +2*(37/100)*(1-σ/5)*third κ*κ 0+(99/50)*(2-σ)*fourth κ

def covariance (u v : Fin 6 → ℝ) : ℝ :=
 (∑ j, (weight j : ℝ)*u j*v j)
 -(3/8)*(∑ j, (weight j : ℝ)*u j)*(∑ j, (weight j : ℝ)*v j)

def denominatorFactor (κ : Fin 6 → ℝ) : ℝ :=
 (2*(151/25)/3-13/25)*theta κ-((151/25)/2)*κ 0^2

def denominator (κ : Fin 6 → ℝ) : ℝ :=
 4*((151/25)-(13/25))*denominatorFactor κ*theta κ^5

def constant (σ a₀ : ℝ) (κ : Fin 6 → ℝ) : ℝ :=
 (σ*(5-2*σ)/10-a₀)*denominator κ

def linear (σ : ℝ) (κ : Fin 6 → ℝ) : ℝ :=
 4*((151/25)-(13/25))*denominatorFactor κ*theta κ^3*baseHom σ κ
 -denominatorFactor κ*covariance (vHom κ) (vHom κ)
 -(151/25)*(covariance (vHom κ) κ)^2-(1/100000000)*denominator κ

def quartic (κ : Fin 6 → ℝ) : ℝ :=
 ((13/25)-1/100000000)*theta κ^4-(1/4)*∑ j, nHom κ j^2

def quadratic (κ : Fin 6 → ℝ) : ℝ :=
 4*((151/25)-(13/25))*denominatorFactor κ*theta κ*quartic κ

@[simp] theorem eval_kappa (x : Fin 5 → ℝ) (j : Fin 6) :
 Expr.eval x (kappa j) = PolynomialChart.spectrumAt x j := by
 fin_cases j <;> simp [kappa,PolynomialChart.spectrumAt,Expr.eval,sub_eq_add_neg]

@[simp] theorem eval_theta (x : Fin 5 → ℝ) :
 Expr.eval x thetaE = theta (PolynomialChart.spectrumAt x) := by
 simp [thetaE,theta,Expr.eval]
@[simp] theorem eval_third (x : Fin 5 → ℝ) :
 Expr.eval x thirdE = third (PolynomialChart.spectrumAt x) := by
 simp [thirdE,third,Expr.eval]
@[simp] theorem eval_fourth (x : Fin 5 → ℝ) :
 Expr.eval x fourthE = fourth (PolynomialChart.spectrumAt x) := by
 simp [fourthE,fourth,Expr.eval]

@[simp] theorem eval_n (x : Fin 5 → ℝ) (j : Fin 6) :
 Expr.eval x (nE j) = nHom (PolynomialChart.spectrumAt x) j := by
 simp [nE,nHom,Expr.eval,rat]; ring
@[simp] theorem eval_v (x : Fin 5 → ℝ) (j : Fin 6) :
 Expr.eval x (vE j) = vHom (PolynomialChart.spectrumAt x) j := by
 simp [vE,vHom,Expr.eval,rat]; ring_nf; simp
@[simp] theorem eval_base (x : Fin 5 → ℝ) (σ : ℚ) :
 Expr.eval x (baseE σ) = baseHom σ (PolynomialChart.spectrumAt x) := by
 simp [baseE,baseHom,Expr.eval,rat]; ring
@[simp] theorem eval_cov (x : Fin 5 → ℝ) (u v : Fin 6 → Expr) :
 Expr.eval x (covE u v) = covariance (fun j => Expr.eval x (u j))
   (fun j => Expr.eval x (v j)) := by
 simp [covE,covariance,Expr.eval,rat,sub_eq_add_neg]
@[simp] theorem eval_d (x : Fin 5 → ℝ) :
 Expr.eval x dE = denominatorFactor (PolynomialChart.spectrumAt x) := by
 simp [dE,denominatorFactor,Expr.eval,rat]; ring
@[simp] theorem eval_denominator (x : Fin 5 → ℝ) :
 Expr.eval x denominatorE = denominator (PolynomialChart.spectrumAt x) := by
 simp [denominatorE,denominator,Expr.eval,rat]
@[simp] theorem eval_constant (x : Fin 5 → ℝ) (σ a₀ : ℚ) :
 Expr.eval x (constantE σ a₀) = constant σ a₀ (PolynomialChart.spectrumAt x) := by
 simp [constantE,constant,Expr.eval,rat]
@[simp] theorem eval_linear (x : Fin 5 → ℝ) (σ : ℚ) :
 Expr.eval x (linearE σ) = linear σ (PolynomialChart.spectrumAt x) := by
 simp [linearE,linear,Expr.eval,rat]; ring
@[simp] theorem eval_quartic (x : Fin 5 → ℝ) :
 Expr.eval x quarticE = quartic (PolynomialChart.spectrumAt x) := by
 simp [quarticE,quartic,Expr.eval,rat]; ring
@[simp] theorem eval_quadratic (x : Fin 5 → ℝ) :
 Expr.eval x quadraticE = quadratic (PolynomialChart.spectrumAt x) := by
 simp [quadraticE,quadratic,Expr.eval,rat]

end
end R7.Core.SpectralPolynomial
