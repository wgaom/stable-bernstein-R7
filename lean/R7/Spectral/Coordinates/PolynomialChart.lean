import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation

namespace R7.PolynomialChart
abbrev Poly := MvPolynomial (Fin 5) ℚ

variable {S : Type*} [CommRing S]

def spectrumAt (x : Fin 5 → S) : Fin 6 → S :=
  let s := x 0
  let g : Fin 4 → S := fun a => x a.succ
  ![5*s, -s-4*g 0-3*g 1-2*g 2-g 3,
    -s+g 0-3*g 1-2*g 2-g 3,
    -s+g 0+2*g 1-2*g 2-g 3,
    -s+g 0+2*g 1+3*g 2-g 3,
    -s+g 0+2*g 1+3*g 2+4*g 3]

end R7.PolynomialChart
