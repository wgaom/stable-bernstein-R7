import R7.Algebra.MinorCertificates

namespace R7.Core.SpectralCertificate
open scoped BigOperators
open R7.Core.Univariate
open R7.Core.Bivariate
open R7.Core.MinorCertificates

def diagonal (p : BiPoly) : ℕ → Poly
 | 0 => Univariate.scale 100 (coefficient p 0)
 | 1 => Univariate.scale 98 (coefficient p 2)
 | n+2 => Univariate.scale 100 (coefficient p (2*(n+2)))
def off (p : BiPoly) (j : ℕ) : Poly := Univariate.scale 50 (coefficient p (2*j+1))
def minus (a b : Poly) : Poly := Univariate.add a (Univariate.neg b)

def bandMinor (p : BiPoly) : ℕ → Poly
 | 0 => [1]
 | 1 => diagonal p 0
 | 2 => minus (Univariate.mul (diagonal p 0) (diagonal p 1)) (Univariate.power (off p 0) 2)
 | 3 => minus (minus (minus
    (Univariate.add (Univariate.mul (Univariate.mul (diagonal p 0) (diagonal p 1)) (diagonal p 2))
      (Univariate.scale 2 (Univariate.mul (Univariate.mul (off p 0) (off p 1)) (coefficient p 2))))
    (Univariate.mul (diagonal p 0) (Univariate.power (off p 1) 2)))
    (Univariate.mul (diagonal p 1) (Univariate.power (coefficient p 2) 2)))
    (Univariate.mul (diagonal p 2) (Univariate.power (off p 0) 2))
 | n+4 => minus (Univariate.mul (diagonal p (n+3)) (bandMinor p (n+3)))
    (Univariate.mul (Univariate.power (off p (n+2)) 2) (bandMinor p (n+2)))

@[simp] theorem evaluate_minus (a b : Poly) (y : ℝ) :
 evaluate (minus a b) y=evaluate a y-evaluate b y := by simp [minus,sub_eq_add_neg]

@[simp] theorem evaluate_diagonal (p : BiPoly) (j : ℕ) (y : ℝ) :
 evaluate (diagonal p j) y = Gram.correctedDiagonal (fun k => evaluate (coefficient p k) y) j := by
 rcases j with _|j
 · simp [diagonal,Gram.correctedDiagonal]
 · rcases j with _|j
   · simp [diagonal,Gram.correctedDiagonal]; ring
   · simp [diagonal,Gram.correctedDiagonal]

@[simp] theorem evaluate_bandMinor (p : BiPoly) (y : ℝ) (n : ℕ) :
 evaluate (bandMinor p n) y =
 Gram.bandDelta (Gram.correctedDiagonal (fun k => evaluate (coefficient p k) y))
   (fun j => 50*evaluate (coefficient p (2*j+1)) y) (evaluate (coefficient p 2) y) n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   rcases n with _|n
   · simp [bandMinor,Gram.bandDelta,evaluate]
   · rcases n with _|n
     · simp [bandMinor,Gram.bandDelta]
     · rcases n with _|n
       · simp [bandMinor,Gram.bandDelta,off]
       · rcases n with _|n
         · simp only [bandMinor,Gram.bandDelta,evaluate_minus,evaluate_add,evaluate_mul,
             evaluate_scale,evaluate_power,evaluate_diagonal,off]
           norm_num
           ring
         · simp only [bandMinor,Gram.bandDelta,evaluate_minus,evaluate_mul,evaluate_power,
             evaluate_diagonal,off,evaluate_scale]
           rw [ih (n+3) (by omega),ih (n+2) (by omega)]
           norm_num

def minorBindings (p : BiPoly) (w : Fin 7 → MinorWitness) : Prop :=
 ∀ j : Fin 7, Univariate.equal (bandMinor p (j.val+1))
   (Univariate.scale (w j).scale (w j).polynomial) = true
instance (p : BiPoly) (w : Fin 7 → MinorWitness) : Decidable (minorBindings p w) :=
 inferInstanceAs (Decidable (∀ _ : Fin 7, _))

theorem corrected_slice_pos (p : BiPoly) (w : Fin 7 → MinorWitness)
    (hmatch : minorBindings p w) (y : ℝ) (hy : 0 ≤ y) (u : ℝ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient p k) y*u^k := by
 apply Gram.corrected_power_polynomial_pos (fun k => evaluate (coefficient p k) y) 4 _ u
 intro j hj
 by_cases hj0 : j=0
 · subst j; norm_num [Gram.bandDelta]
 · let i : Fin 7 := ⟨j-1,by omega⟩
   have hi : i.val+1=j := by dsimp [i]; omega
   have hm := Univariate.equal_sound _ _ (hmatch i) y
   rw [evaluate_bandMinor,evaluate_scale,hi] at hm
   rw [hm]
   exact mul_pos (by exact_mod_cast (w i).scale_pos) ((w i).positive y hy)

def ordinaryBindings (p : BiPoly) (w : Fin 5 → MinorWitness) : Prop :=
 ∀ j : Fin 5, Univariate.equal (minorPolynomial p (j.val+1))
   (Univariate.scale (w j).scale (w j).polynomial) = true
instance (p : BiPoly) (w : Fin 5 → MinorWitness) : Decidable (ordinaryBindings p w) :=
 inferInstanceAs (Decidable (∀ _ : Fin 5, _))

theorem ordinary_slice_pos (p : BiPoly) (w : Fin 5 → MinorWitness)
    (hmatch : ordinaryBindings p w) (y : ℝ) (hy : 0 ≤ y) (u : ℝ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient p k) y*u^k := by
 apply Gram.power_polynomial_pos (fun k => evaluate (coefficient p k) y) 4 _ u
 intro j hj
 by_cases hj0 : j=0
 · subst j; norm_num [Gram.delta]
 · let i : Fin 5 := ⟨j-1,by omega⟩
   have hi : i.val+1=j := by dsimp [i]; omega
   have hm := Univariate.equal_sound _ _ (hmatch i) y
   rw [evaluate_minorPolynomial,evaluate_scale,hi] at hm
   rw [hm]
   exact mul_pos (by exact_mod_cast (w i).scale_pos) ((w i).positive y hy)

end R7.Core.SpectralCertificate
