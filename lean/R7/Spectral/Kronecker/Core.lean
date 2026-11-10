import R7.Spectral.PolynomialCompute
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import R7.Algebra.Kronecker
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import R7.Algebra.IntegerHorner
import R7.Algebra.RationalExpression
import R7.Algebra.IntegerSparseOperations

namespace R7.Core.SpectralCoefficient.Kronecker
open R7.ComputablePolynomial

/-- Structural homogeneous degree; no polynomial normalization is involved. -/
def homogeneousDegree : Expr → Option ℕ
  | .rat _ => some 0
  | .var _ => some 1
  | .add a b => match homogeneousDegree a, homogeneousDegree b with
    | some m, some n => if m = n then some m else none
    | _, _ => none
  | .neg a => homogeneousDegree a
  | .mul a b => match homogeneousDegree a, homogeneousDegree b with
    | some m, some n => some (m + n)
    | _, _ => none
  | .pow a n => (homogeneousDegree a).map (fun m => m * n)

theorem homogeneousDegree_sound (e : Expr) (d : ℕ)
    (h : homogeneousDegree e = some d) : e.denote.IsHomogeneous d := by
  induction e generalizing d with
  | rat q =>
    simp only [homogeneousDegree, Option.some.injEq] at h
    subst d
    exact MvPolynomial.isHomogeneous_C _ _
  | var i =>
    simp only [homogeneousDegree, Option.some.injEq] at h
    subst d
    exact MvPolynomial.isHomogeneous_X _ _
  | neg a ih =>
    exact (ih d h).neg
  | add a b iha ihb =>
    cases ha : homogeneousDegree a with
    | none => simp [homogeneousDegree, ha] at h
    | some m =>
      cases hb : homogeneousDegree b with
      | none => simp [homogeneousDegree, ha, hb] at h
      | some n =>
        simp only [homogeneousDegree, ha, hb] at h
        by_cases he : m = n
        · simp only [he, ite_true, Option.some.injEq] at h
          subst d
          subst n
          exact (iha _ ha).add (ihb _ hb)
        · simp [he] at h
  | mul a b iha ihb =>
    cases ha : homogeneousDegree a with
    | none => simp [homogeneousDegree, ha] at h
    | some m =>
      cases hb : homogeneousDegree b with
      | none => simp [homogeneousDegree, ha, hb] at h
      | some n =>
        simp only [homogeneousDegree, ha, hb, Option.some.injEq] at h
        subst d
        exact (iha _ ha).mul (ihb _ hb)
  | pow a n ih =>
    cases ha : homogeneousDegree a with
    | none => simp [homogeneousDegree, ha] at h
    | some m =>
      simp only [homogeneousDegree, ha, Option.map_some, Option.some.injEq] at h
      subst d
      exact (ih _ ha).pow n

/-- A fixed finite sum is cheaper to check than a Finsupp degree expression. -/
def totalExp (e : Exp) : ℕ := e 0 + e 1 + e 2 + e 3 + e 4

theorem finsupp_sum (e : Fin 5 →₀ ℕ) :
    (∑ i ∈ e.support, e i) = totalExp e := by
  have hh : (∑ i ∈ e.support, e i) = ∑ i : Fin 5, e i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hn
    simpa only [Finsupp.mem_support_iff, not_not] using hn
  simpa [totalExp, Fin.sum_univ_succ, add_assoc] using hh

theorem interpret_homogeneous (p : R7.Core.SpectralCoefficient.KeyPoly) (d : ℕ)
    (h : ∀ a ∈ p, totalExp a.exp = d) :
    (R7.Core.SpectralCoefficient.interpretKey p).IsHomogeneous d := by
  induction p with
  | nil => exact MvPolynomial.isHomogeneous_zero _ _ _
  | cons a ps ih =>
    apply MvPolynomial.IsHomogeneous.add
    · apply MvPolynomial.isHomogeneous_monomial
      rw [Finsupp.degree_apply, finsupp_sum]
      simpa [totalExp, exponent] using h a (by simp)
    · exact ih (fun b hb => h b (by simp [hb]))

end R7.Core.SpectralCoefficient.Kronecker

namespace R7.Core.SpectralCoefficient.Kronecker
open Polynomial
open scoped BigOperators

/-- Omit the homogenizing variable, recovering it from the homogeneous degree. -/
def encode (base : ℕ) (e : Fin 5 → ℕ) : ℕ :=
  Nat.ofDigits base [e 1, e 2, e 3, e 4]

def weight (base : ℕ) : Fin 5 → ℕ := ![0, 1, base, base^2, base^3]

theorem encode_injective_of_degree {base : ℕ} (hb : 1 < base)
    {e f : Fin 5 → ℕ} {d : ℕ}
    (he : ∀ i, e i < base) (hf : ∀ i, f i < base)
    (hed : totalExp e = d) (hfd : totalExp f = d)
    (h : encode base e = encode base f) : e = f := by
  have hl : [e 1,e 2,e 3,e 4] = [f 1,f 2,f 3,f 4] :=
    Nat.ofDigits_inj_of_len_eq hb rfl
      (by simp only [List.mem_cons]; aesop)
      (by simp only [List.mem_cons]; aesop) h
  have h1 : e 1 = f 1 := List.cons.inj hl |>.1
  have h2 : e 2 = f 2 := List.cons.inj (List.cons.inj hl |>.2) |>.1
  have h3 : e 3 = f 3 := List.cons.inj (List.cons.inj (List.cons.inj hl |>.2) |>.2) |>.1
  have h4 : e 4 = f 4 := by
    simpa using (List.cons.inj (List.cons.inj (List.cons.inj hl |>.2) |>.2) |>.2)
  simp only [totalExp] at hed hfd
  funext i
  fin_cases i <;> simp_all
  omega

theorem substitution_monomial (base : ℕ) (e : Fin 5 →₀ ℕ) (c : ℚ) :
    MvPolynomial.eval₂Hom Polynomial.C (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)
      (MvPolynomial.monomial e c) = Polynomial.monomial (encode base e) c := by
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype]
  · simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    have hh : (∑ i : Fin 5, weight base i * e i) = encode base e := by
      simp [weight, encode, Nat.ofDigits, Fin.sum_univ_succ]
      ring
    rw [hh, C_mul_X_pow_eq_monomial]
  · intro i
    simp

theorem substitution_eq_pack (base : ℕ) (p : MvPolynomial (Fin 5) ℚ) :
    MvPolynomial.eval₂Hom Polynomial.C (fun i => (Polynomial.X : Polynomial ℚ)^weight base i) p =
      ∑ e ∈ p.support, Polynomial.monomial (encode base e) (MvPolynomial.coeff e p) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [map_sum, substitution_monomial]

/-- Kronecker substitution is injective on a checked homogeneous degree. -/
theorem substitution_zero_implies_zero (base : ℕ) (hb : 1 < base)
    (p : MvPolynomial (Fin 5) ℚ) (d : ℕ)
    (hdegree : ∀ e ∈ p.support, totalExp e = d)
    (hcoords : ∀ e ∈ p.support, ∀ i, e i < base)
    (hz : MvPolynomial.eval₂Hom Polynomial.C
      (fun i => (Polynomial.X : Polynomial ℚ)^weight base i) p = 0) : p = 0 := by
  classical
  have hi : Set.InjOn (fun e : Fin 5 →₀ ℕ => encode base e) (↑p.support : Set _) := by
    intro e he f hf h
    apply DFunLike.ext
    intro i
    exact congrFun (encode_injective_of_degree hb (hcoords e he) (hcoords f hf)
      (hdegree e he) (hdegree f hf) h) i
  ext e
  by_cases he : e ∈ p.support
  · have hh := congrArg (fun q : Polynomial ℚ => q.coeff (encode base e)) hz
    rw [substitution_eq_pack] at hh
    simp only [finset_sum_coeff, coeff_zero] at hh
    rw [Finset.sum_eq_single e] at hh
    · simpa using hh
    · intro f hf hfe
      simp only [coeff_monomial]
      split_ifs with h
      · exact False.elim (hfe (hi hf he h))
      · rfl
    · simp [he]
  · simp only [MvPolynomial.coeff_zero]
    by_contra hc
    exact he (MvPolynomial.mem_support_iff.mpr hc)

/-- The homogeneous degree itself supplies every coordinate bound, so no
expanded-polynomial support needs to be enumerated by the concrete checker. -/
theorem homogeneous_eq_of_substitution_eq (base : ℕ) (hb : 1 < base)
    (p q : MvPolynomial (Fin 5) ℚ) (d : ℕ) (hd : d < base)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d)
    (he : MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i) p =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i) q) : p = q := by
  apply sub_eq_zero.mp
  have hh := hp.sub hq
  apply substitution_zero_implies_zero base hb (p - q) d
  · intro e he
    have hdeg := hh.degree_eq_sum_deg_support he
    rw [finsupp_sum] at hdeg
    exact hdeg.symm
  · intro e he i
    have hdeg := hh.degree_eq_sum_deg_support he
    rw [finsupp_sum] at hdeg
    simp only [totalExp] at hdeg
    fin_cases i
    · change e 0 < base; omega
    · change e 1 < base; omega
    · change e 2 < base; omega
    · change e 3 < base; omega
    · change e 4 < base; omega
  · simpa only [map_sub, sub_eq_zero] using he

end R7.Core.SpectralCoefficient.Kronecker

namespace R7.Core.SpectralCoefficient.Kronecker.FullSubstitution
open R7.ComputablePolynomial
open Polynomial
open scoped BigOperators

def code (e : Fin 5 → ℕ) : ℕ := Nat.ofDigits 32 [e 0,e 1,e 2,e 3,e 4]
def weight : Fin 5 → ℕ := ![1,32,1024,32768,1048576]

theorem code_eq_expCode (e : Fin 5 → ℕ) : code e = R7.Core.SpectralCoefficient.expCode e := by
  simp [code, Nat.ofDigits, R7.Core.SpectralCoefficient.expCode]

theorem code_injective {e f : Fin 5 → ℕ}
    (he : ∀ i, e i < 32) (hf : ∀ i, f i < 32) (h : code e = code f) : e = f := by
  have hl : [e 0,e 1,e 2,e 3,e 4] = [f 0,f 1,f 2,f 3,f 4] :=
    Nat.ofDigits_inj_of_len_eq (by decide) rfl
      (by simp only [List.mem_cons]; aesop)
      (by simp only [List.mem_cons]; aesop) h
  simp only [List.cons.injEq, and_true] at hl
  rcases hl with ⟨h0,h1,h2,h3,h4⟩
  funext i
  fin_cases i <;> assumption

noncomputable def apply : R7.PolynomialChart.Poly →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => (Polynomial.X : Polynomial ℚ)^weight i)

theorem apply_monomial (e : Fin 5 →₀ ℕ) (c : ℚ) :
    apply (MvPolynomial.monomial e c) = Polynomial.monomial (code e) c := by
  rw [apply, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype]
  · simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    have hh : (∑ i : Fin 5, weight i * e i) = code e := by
      simp [weight, code, Nat.ofDigits, Fin.sum_univ_succ]
      omega
    rw [hh, C_mul_X_pow_eq_monomial]
  · intro i
    simp

theorem apply_eq_pack (p : MvPolynomial (Fin 5) ℚ) :
    apply p = ∑ e ∈ p.support, Polynomial.monomial (code e) (MvPolynomial.coeff e p) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [map_sum, apply_monomial]

theorem zero_implies_zero (p : MvPolynomial (Fin 5) ℚ)
    (hcoords : ∀ e ∈ p.support, ∀ i, e i < 32) (hz : apply p = 0) : p = 0 := by
  classical
  have hi : Set.InjOn (fun e : Fin 5 →₀ ℕ => code e) (↑p.support : Set _) := by
    intro e he f hf h
    apply DFunLike.ext
    intro i
    exact congrFun (code_injective (hcoords e he) (hcoords f hf) h) i
  ext e
  by_cases he : e ∈ p.support
  · have hh := congrArg (fun q : Polynomial ℚ => q.coeff (code e)) hz
    rw [apply_eq_pack] at hh
    simp only [finset_sum_coeff, coeff_zero] at hh
    rw [Finset.sum_eq_single e] at hh
    · simpa using hh
    · intro f hf hfe
      simp only [coeff_monomial]
      split_ifs with h
      · exact False.elim (hfe (hi hf he h))
      · rfl
    · simp [he]
  · simp only [MvPolynomial.coeff_zero]
    by_contra hc
    exact he (MvPolynomial.mem_support_iff.mpr hc)

theorem homogeneous_eq (p q : MvPolynomial (Fin 5) ℚ) (d : ℕ) (hd : d < 32)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) (he : apply p = apply q) : p = q := by
  apply sub_eq_zero.mp
  have hh := hp.sub hq
  apply zero_implies_zero (p-q)
  · intro e he i
    have hdeg := hh.degree_eq_sum_deg_support he
    rw [finsupp_sum] at hdeg
    simp only [totalExp] at hdeg
    fin_cases i
    · change e 0 < 32; omega
    · change e 1 < 32; omega
    · change e 2 < 32; omega
    · change e 3 < 32; omega
    · change e 4 < 32; omega
  · simpa only [map_sub, sub_eq_zero] using he

end R7.Core.SpectralCoefficient.Kronecker.FullSubstitution

namespace R7.Core.SpectralCoefficient.Kronecker
open R7.ComputablePolynomial
open R7.Core.SpectralCoefficient (expEqual expEqual_eq_true)

structure Term where
  key : ℕ
  exp : Exp
  value : ℤ
  deriving DecidableEq
abbrev KeyPoly := List Term

noncomputable def interpretKey : KeyPoly → PolynomialChart.Poly
 | [] => 0
 | a::ps => MvPolynomial.monomial (exponent a.exp) (a.value : ℚ)+interpretKey ps

def collectKey (a : Term) (p : KeyPoly) : KeyPoly :=
  List.rec (motive := fun _ => Term → KeyPoly)
    (fun a => if a.value=0 then [] else [a])
    (fun b _ rec a => if a.key=b.key ∧ expEqual a.exp b.exp = true then
      rec ⟨a.key,a.exp,a.value+b.value⟩
      else if a.value=0 then rec b else a::rec b) p a

def mergeKey (n : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => p++q)
    (fun _ rec p q => match p,q with
      | [],q => q
      | p,[] => p
      | a::p,b::q => if a.key ≤ b.key then a::rec p (b::q)
          else b::rec (a::p) q) n p q

def sortKey (n : ℕ) (p : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly) (fun p => p)
    (fun _ rec p => match p with
      | [] => []
      | [a] => [a]
      | p => mergeKey p.length (rec (p.take (p.length/2)))
          (rec (p.drop (p.length/2)))) n p

def normalizeKey (p : KeyPoly) : KeyPoly :=
 match sortKey 32 p with
 | [] => []
 | a::ps => collectKey a ps

theorem collectKey_nil (a : Term) : collectKey a [] =
    (if a.value=0 then [] else [a]) := rfl

theorem collectKey_cons (a b : Term) (p : KeyPoly) : collectKey a (b::p) =
    (if a.key=b.key ∧ a.exp=b.exp then collectKey ⟨a.key,a.exp,a.value+b.value⟩ p
    else if a.value=0 then collectKey b p else a::collectKey b p) := by
  change (if a.key=b.key ∧ expEqual a.exp b.exp = true then
    collectKey ⟨a.key,a.exp,a.value+b.value⟩ p
    else if a.value=0 then collectKey b p else a::collectKey b p) = _
  simp only [expEqual_eq_true]

theorem mergeKey_zero (p q : KeyPoly) : mergeKey 0 p q=p++q := rfl

theorem mergeKey_succ (n : ℕ) (p q : KeyPoly) : mergeKey (n+1) p q=
    (match p,q with
    | [],q => q
    | p,[] => p
    | a::p,b::q => if a.key ≤ b.key then a::mergeKey n p (b::q)
        else b::mergeKey n (a::p) q) := rfl

theorem sortKey_succ (n : ℕ) (p : KeyPoly) : sortKey (n+1) p=
    (match p with
    | [] => []
    | [a] => [a]
    | p => mergeKey p.length (sortKey n (p.take (p.length/2)))
        (sortKey n (p.drop (p.length/2)))) := rfl

theorem interpret_collectKey (a : Term) (p : KeyPoly) :
    interpretKey (collectKey a p) = MvPolynomial.monomial (exponent a.exp) (a.value : ℚ)+interpretKey p := by
  induction p generalizing a with
  | nil => by_cases ha : a.value=0 <;> simp [collectKey_nil,interpretKey,ha]
  | cons b ps ih =>
    by_cases hab : a.key=b.key ∧ a.exp=b.exp
    · simp only [collectKey_cons,hab,and_self,ite_true,ih,interpretKey]
      rw [Int.cast_add, map_add]
      abel
    · by_cases ha : a.value=0
      · simp [collectKey_cons,hab,ha,ih,interpretKey]
      · simp only [collectKey_cons,hab,ha,ite_false,interpretKey,ih]

@[simp] theorem interpretKey_append (p q : KeyPoly) : interpretKey (p++q)=interpretKey p+interpretKey q := by
  induction p with
  | nil => simp [interpretKey]
  | cons a p ih => simp only [List.cons_append,interpretKey,ih]; abel

theorem interpret_mergeKey (n : ℕ) (p q : KeyPoly) :
    interpretKey (mergeKey n p q)=interpretKey p+interpretKey q := by
  induction n generalizing p q with
  | zero => simp [mergeKey_zero]
  | succ n ih => cases p with
    | nil => simp [mergeKey_succ,interpretKey]
    | cons a p => cases q with
      | nil => simp [mergeKey_succ,interpretKey]
      | cons b q =>
        by_cases h : a.key ≤ b.key
        · simp only [mergeKey_succ,h,ite_true,interpretKey,ih]; abel
        · simp only [mergeKey_succ,h,ite_false,interpretKey,ih]; abel

theorem interpret_sortKey (n : ℕ) (p : KeyPoly) : interpretKey (sortKey n p)=interpretKey p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => cases p with
    | nil => rfl
    | cons a p => cases p with
      | nil => rfl
      | cons b p =>
        simp only [sortKey_succ,interpret_mergeKey,ih]
        rw [← interpretKey_append,List.take_append_drop]

@[simp] theorem interpret_normalizeKey (p : KeyPoly) : interpretKey (normalizeKey p)=interpretKey p := by
  have hh := interpret_sortKey 32 p
  cases he : sortKey 32 p with
  | nil => simpa [normalizeKey,he] using hh
  | cons a ps => simpa only [normalizeKey,he,interpret_collectKey,interpretKey] using hh

/-- Combine adjacent equal terms. Inputs produced by the checker are sorted. -/
def compressKey (p : KeyPoly) : KeyPoly :=
  match p with
  | [] => []
  | a :: ps => collectKey a ps

@[simp] theorem interpret_compressKey (p : KeyPoly) :
    interpretKey (compressKey p) = interpretKey p := by
  cases p <;> simp [compressKey, interpretKey, interpret_collectKey]

/-- Merge already sorted sparse polynomials without sorting their concatenation. -/
def addKey (p q : KeyPoly) := compressKey (mergeKey (p.length + q.length) p q)
def negKey (p : KeyPoly) := p.map (fun a => {a with value := -a.value})
def mulTerm (a b : Term) : Term := ⟨a.key+b.key,a.exp+b.exp,a.value*b.value⟩
/-- Balanced multiplication combines equal terms before forming the next level.
The fallback makes the operation total independently of any size bound. -/
def mulKeyAux (fuel : ℕ) (p q : KeyPoly) : KeyPoly :=
  Nat.rec (motive := fun _ => KeyPoly → KeyPoly → KeyPoly)
    (fun p q => normalizeKey (p.flatMap (fun a => q.map (mulTerm a))))
    (fun _ rec p q => match p with
      | [] => []
      | [a] => compressKey (q.map (mulTerm a))
      | p => addKey (rec (p.take (p.length / 2)) q)
          (rec (p.drop (p.length / 2)) q)) fuel p q

def mulKey (p q : KeyPoly) := mulKeyAux 32 p q
def constantKey (a : ℤ) : KeyPoly := if a=0 then [] else [⟨0,0,a⟩]
def varKey (i : Fin 5) : KeyPoly := [⟨32^i.val,(fun j => if j=i then 1 else 0),1⟩]
def powerKey (p : KeyPoly) (n : ℕ) : KeyPoly :=
  Nat.rec (constantKey 1) (fun _ prev => mulKey prev p) n

theorem powerKey_zero (p : KeyPoly) : powerKey p 0=constantKey 1 := rfl

theorem powerKey_succ (p : KeyPoly) (n : ℕ) :
    powerKey p (n+1)=mulKey (powerKey p n) p := rfl

@[simp] theorem interpretKey_add (p q : KeyPoly) : interpretKey (addKey p q)=interpretKey p+interpretKey q := by simp [addKey, interpret_mergeKey]
@[simp] theorem interpretKey_neg (p : KeyPoly) : interpretKey (negKey p)= -interpretKey p := by
  induction p with
  | nil => simp [negKey,interpretKey]
  | cons a p ih => simp only [negKey,List.map_cons,interpretKey,Int.cast_neg,map_neg,neg_add_rev] at *; rw [ih]; abel
@[simp] theorem interpretKey_mulTerm (a : Term) (q : KeyPoly) :
    interpretKey (q.map (mulTerm a)) = MvPolynomial.monomial (exponent a.exp) (a.value : ℚ)*interpretKey q := by
  induction q with
  | nil => simp [interpretKey]
  | cons b q ih =>
    simp only [List.map_cons,interpretKey,mulTerm,exponent_add,Int.cast_mul,← MvPolynomial.monomial_mul,mul_add]
    exact congrArg (fun z => MvPolynomial.monomial (exponent a.exp) (a.value : ℚ) *
      MvPolynomial.monomial (exponent b.exp) (b.value : ℚ)+z) ih
theorem interpretKey_flatMap_mulTerm (p q : KeyPoly) :
    interpretKey (p.flatMap (fun a => q.map (mulTerm a))) =
      interpretKey p * interpretKey q := by
  induction p with
  | nil => simp [interpretKey]
  | cons a p ih =>
    simp only [List.flatMap_cons, interpretKey_append, interpretKey_mulTerm, ih, interpretKey]
    ring

theorem interpretKey_mulKeyAux (fuel : ℕ) (p q : KeyPoly) :
    interpretKey (mulKeyAux fuel p q) = interpretKey p * interpretKey q := by
  induction fuel generalizing p q with
  | zero => simp [mulKeyAux, interpretKey_flatMap_mulTerm]
  | succ fuel ih =>
    cases p with
    | nil => simp [mulKeyAux, interpretKey]
    | cons a ps =>
      cases ps with
      | nil => simp [mulKeyAux, interpretKey]
      | cons b ps =>
        change interpretKey (addKey
          (mulKeyAux fuel ((a :: b :: ps).take ((a :: b :: ps).length / 2)) q)
          (mulKeyAux fuel ((a :: b :: ps).drop ((a :: b :: ps).length / 2)) q)) = _
        rw [interpretKey_add, ih, ih, ← add_mul, ← interpretKey_append,
          List.take_append_drop]

@[simp] theorem interpretKey_mul (p q : KeyPoly) : interpretKey (mulKey p q)=interpretKey p*interpretKey q := by
  exact interpretKey_mulKeyAux 32 p q
@[simp] theorem interpretKey_constant (a : ℤ) : interpretKey (constantKey a)=MvPolynomial.C (a : ℚ) := by
  by_cases ha : a=0 <;> simp [constantKey,interpretKey,ha]
@[simp] theorem interpretKey_power (p : KeyPoly) (n : ℕ) : interpretKey (powerKey p n)=interpretKey p^n := by
  induction n with
  | zero => simp [powerKey_zero,interpretKey_constant]
  | succ n ih => simp only [powerKey_succ,interpretKey_mul,ih,pow_succ]

/-- Scalar multiplication does not introduce coefficient gcd computations. -/
def scaleKey (c : ℤ) (p : KeyPoly) : KeyPoly :=
  p.map (fun a => ⟨a.key, a.exp, c * a.value⟩)

@[simp] theorem interpretKey_scale (c : ℤ) (p : KeyPoly) :
    interpretKey (scaleKey c p) = MvPolynomial.C (c : ℚ) * interpretKey p := by
  induction p with
  | nil => simp [scaleKey, interpretKey]
  | cons a ps ih =>
    change MvPolynomial.monomial (exponent a.exp) ((c * a.value : ℤ) : ℚ) +
      interpretKey (scaleKey c ps) = _
    rw [Int.cast_mul, ← MvPolynomial.C_mul_monomial, ih, interpretKey, mul_add]

def termEqual (a b : Term) : Bool :=
  (a.key == b.key) && (a.value == b.value) &&
    (List.finRange 5).all (fun i => a.exp i == b.exp i)

theorem termEqual_sound (a b : Term) (h : termEqual a b=true) : a=b := by
  have hs := Bool.and_eq_true_iff.mp h
  have hkv := Bool.and_eq_true_iff.mp hs.1
  have hk : a.key=b.key := by simpa using hkv.1
  have hv : a.value=b.value := by simpa using hkv.2
  have he : a.exp=b.exp := by
    funext i
    have hh := (List.all_eq_true.mp hs.2) i (List.mem_finRange i)
    simpa using hh
  cases a; cases b
  simp_all

def keyPolyEqual : KeyPoly → KeyPoly → Bool
 | [],[] => true
 | a::p,b::q => termEqual a b && keyPolyEqual p q
 | _,_ => false

theorem keyPolyEqual_sound (p q : KeyPoly) (h : keyPolyEqual p q=true) : p=q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [keyPolyEqual]
  | cons a p ih => cases q with
    | nil => simp [keyPolyEqual] at h
    | cons b q =>
      have hs := Bool.and_eq_true_iff.mp h
      rw [termEqual_sound a b hs.1,ih q hs.2]

end R7.Core.SpectralCoefficient.Kronecker

namespace R7.Core.SpectralCoefficient.Kronecker
open R7.ComputablePolynomial

/-- Check the common-denominator representation of a rational polynomial. -/
def scaledTermEq (d : ℕ) (p : R7.Core.SpectralCoefficient.Term) (z : Term) : Bool :=
  (p.key == z.key) && R7.Core.SpectralCoefficient.expEqual p.exp z.exp &&
    ((z.value : ℚ) == (d : ℚ) * p.value)

def scaledEq (d : ℕ) : R7.Core.SpectralCoefficient.KeyPoly → KeyPoly → Bool
  | [], [] => true
  | p :: ps, z :: zs => scaledTermEq d p z && scaledEq d ps zs
  | _, _ => false

theorem scaledTermEq_sound (d : ℕ) (p : R7.Core.SpectralCoefficient.Term)
    (z : Term) (h : scaledTermEq d p z = true) :
    MvPolynomial.monomial (exponent z.exp) (z.value : ℚ) =
      MvPolynomial.C (d : ℚ) * MvPolynomial.monomial (exponent p.exp) p.value := by
  have hs := Bool.and_eq_true_iff.mp h
  have hk := Bool.and_eq_true_iff.mp hs.1
  have he : p.exp = z.exp := R7.Core.SpectralCoefficient.expEqual_eq_true _ _ |>.mp hk.2
  have hv : (z.value : ℚ) = (d : ℚ) * p.value := by simpa using hs.2
  rw [he, hv, MvPolynomial.C_mul_monomial]

theorem scaledEq_sound (d : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (z : KeyPoly) (h : scaledEq d p z = true) :
    interpretKey z = MvPolynomial.C (d : ℚ) * R7.Core.SpectralCoefficient.interpretKey p := by
  induction p generalizing z with
  | nil =>
    cases z with
    | nil => simp [interpretKey, R7.Core.SpectralCoefficient.interpretKey]
    | cons a zs => simp [scaledEq] at h
  | cons a ps ih =>
    cases z with
    | nil => simp [scaledEq] at h
    | cons b zs =>
      have hs := Bool.and_eq_true_iff.mp h
      rw [interpretKey, R7.Core.SpectralCoefficient.interpretKey,
        scaledTermEq_sound d a b hs.1, ih zs hs.2, mul_add]

/-- Pair a polynomial's keys and exponents with integer coefficients. -/
def withCoefficients : R7.Core.SpectralCoefficient.KeyPoly → List ℤ → KeyPoly
  | p :: ps, z :: zs => ⟨p.key, p.exp, z⟩ :: withCoefficients ps zs
  | _, _ => []

def scaledCoefficientsEq (d : ℕ) :
    R7.Core.SpectralCoefficient.KeyPoly → List ℤ → Bool
  | [], [] => true
  | p :: ps, z :: zs => ((z : ℚ) == (d : ℚ) * p.value) &&
      scaledCoefficientsEq d ps zs
  | _, _ => false

theorem scaledCoefficientsEq_sound (d : ℕ)
    (p : R7.Core.SpectralCoefficient.KeyPoly) (zs : List ℤ)
    (h : scaledCoefficientsEq d p zs = true) :
    interpretKey (withCoefficients p zs) =
      MvPolynomial.C (d : ℚ) * R7.Core.SpectralCoefficient.interpretKey p := by
  induction p generalizing zs with
  | nil =>
    cases zs with
    | nil => simp [withCoefficients, interpretKey, R7.Core.SpectralCoefficient.interpretKey]
    | cons a zs => simp [scaledCoefficientsEq] at h
  | cons a ps ih =>
    cases zs with
    | nil => simp [scaledCoefficientsEq] at h
    | cons b zs =>
      have hs := Bool.and_eq_true_iff.mp h
      have hv : (b : ℚ) = (d : ℚ) * a.value := by simpa using hs.1
      simp only [withCoefficients, interpretKey, R7.Core.SpectralCoefficient.interpretKey]
      rw [hv, ← MvPolynomial.C_mul_monomial, ih zs hs.2, mul_add]

/-- Check coefficient scaling by integer cross multiplication. -/
def scaledCoefficientsEqCross (d : ℕ) :
    R7.Core.SpectralCoefficient.KeyPoly → List ℤ → Bool
  | [], [] => true
  | p :: ps, z :: zs => (z * (p.value.den : ℤ) == p.value.num * (d : ℤ)) &&
      scaledCoefficientsEqCross d ps zs
  | _, _ => false

/-- Candidate numerator for scaling by `D`, validated by cross multiplication. -/
def scaledNumerator (D : ℕ) (q : ℚ) : ℤ := q.num * (D / q.den : ℕ)

theorem scaledCoefficientCross_sound (d : ℕ) (q : ℚ) (z : ℤ)
    (h : z * (q.den : ℤ) == q.num * (d : ℤ)) :
    (z : ℚ) = (d : ℚ) * q := by
  have hi : z * (q.den : ℤ) = q.num * (d : ℤ) := by simpa using h
  have hc := congrArg (fun n : ℤ => (n : ℚ)) hi
  simp only [Int.cast_mul, Int.cast_natCast] at hc
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt q.den_pos)
  have hq : q * (q.den : ℚ) = q.num := ((div_eq_iff hden).mp (Rat.num_div_den q)).symm
  apply mul_right_cancel₀ hden
  calc
    (z : ℚ) * (q.den : ℚ) = (q.num : ℚ) * (d : ℚ) := hc
    _ = ((d : ℚ) * q) * (q.den : ℚ) := by rw [mul_assoc, hq, mul_comm]

theorem scaledCoefficientsEqCross_sound (d : ℕ)
    (p : R7.Core.SpectralCoefficient.KeyPoly) (zs : List ℤ)
    (h : scaledCoefficientsEqCross d p zs = true) :
    interpretKey (withCoefficients p zs) =
      MvPolynomial.C (d : ℚ) * R7.Core.SpectralCoefficient.interpretKey p := by
  induction p generalizing zs with
  | nil =>
    cases zs with
    | nil => simp [withCoefficients, interpretKey, R7.Core.SpectralCoefficient.interpretKey]
    | cons a zs => simp [scaledCoefficientsEqCross] at h
  | cons a ps ih =>
    cases zs with
    | nil => simp [scaledCoefficientsEqCross] at h
    | cons b zs =>
      have hs := Bool.and_eq_true_iff.mp h
      have hv := scaledCoefficientCross_sound d a.value b hs.1
      simp only [withCoefficients, interpretKey, R7.Core.SpectralCoefficient.interpretKey]
      rw [hv, ← MvPolynomial.C_mul_monomial, ih zs hs.2, mul_add]

/-- Integer convolution proves the rational product identity. -/
theorem mul_sound (dp dq : ℕ) (hdp : dp ≠ 0) (hdq : dq ≠ 0)
    (p q r : R7.Core.SpectralCoefficient.KeyPoly) (zp zq zr : KeyPoly)
    (hp : scaledEq dp p zp = true) (hq : scaledEq dq q zq = true)
    (hr : scaledEq (dp * dq) r zr = true)
    (hm : keyPolyEqual (mulKey zp zq) zr = true) :
    R7.Core.SpectralCoefficient.interpretKey r =
      R7.Core.SpectralCoefficient.interpretKey p *
      R7.Core.SpectralCoefficient.interpretKey q := by
  have hi := congrArg interpretKey (keyPolyEqual_sound _ _ hm)
  rw [interpretKey_mul, scaledEq_sound dp p zp hp,
    scaledEq_sound dq q zq hq, scaledEq_sound (dp * dq) r zr hr] at hi
  have hprod : MvPolynomial.C ((dp * dq : ℕ) : ℚ) =
      (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) * MvPolynomial.C (dq : ℚ) := by
    simp
  rw [hprod] at hi
  have hnonzero : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) *
      MvPolynomial.C (dq : ℚ) ≠ 0 := by
    simp [hdp, hdq]
  apply mul_left_cancel₀ hnonzero
  calc
    _ = (MvPolynomial.C (dp : ℚ) * R7.Core.SpectralCoefficient.interpretKey p) *
        (MvPolynomial.C (dq : ℚ) * R7.Core.SpectralCoefficient.interpretKey q) := hi.symm
    _ = _ := by ring

theorem mul_semantic_of_scaled (dp dq dr k : ℕ) (hdp : dp ≠ 0) (hdq : dq ≠ 0)
    (hfactor : dp * dq = k * dr)
    (p q r : R7.Core.SpectralCoefficient.KeyPoly) (zp zq zr : KeyPoly)
    (hp : interpretKey zp = MvPolynomial.C (dp : ℚ) * R7.Core.SpectralCoefficient.interpretKey p)
    (hq : interpretKey zq = MvPolynomial.C (dq : ℚ) * R7.Core.SpectralCoefficient.interpretKey q)
    (hr : interpretKey zr = MvPolynomial.C (dr : ℚ) * R7.Core.SpectralCoefficient.interpretKey r)
    (hi : interpretKey zp * interpretKey zq =
      MvPolynomial.C (k : ℚ) * interpretKey zr) :
    R7.Core.SpectralCoefficient.interpretKey r =
      R7.Core.SpectralCoefficient.interpretKey p *
      R7.Core.SpectralCoefficient.interpretKey q := by
  rw [hp, hq, hr] at hi
  have hprod : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) * MvPolynomial.C (dq : ℚ) =
      MvPolynomial.C (k : ℚ) * MvPolynomial.C (dr : ℚ) := by
    simpa only [← map_mul, ← Nat.cast_mul] using congrArg
      (fun n : ℕ => (MvPolynomial.C (n : ℚ) : PolynomialChart.Poly)) hfactor
  have hnonzero : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) *
      MvPolynomial.C (dq : ℚ) ≠ 0 := by simp [hdp, hdq]
  apply mul_left_cancel₀ hnonzero
  calc
    _ = MvPolynomial.C (k : ℚ) * MvPolynomial.C (dr : ℚ) *
        R7.Core.SpectralCoefficient.interpretKey r := by rw [hprod]
    _ = _ := by linear_combination -hi

theorem mul_of_scaled (dp dq dr k : ℕ) (hdp : dp ≠ 0) (hdq : dq ≠ 0)
    (hfactor : dp * dq = k * dr)
    (p q r : R7.Core.SpectralCoefficient.KeyPoly) (zp zq zr : KeyPoly)
    (hp : interpretKey zp = MvPolynomial.C (dp : ℚ) * R7.Core.SpectralCoefficient.interpretKey p)
    (hq : interpretKey zq = MvPolynomial.C (dq : ℚ) * R7.Core.SpectralCoefficient.interpretKey q)
    (hr : interpretKey zr = MvPolynomial.C (dr : ℚ) * R7.Core.SpectralCoefficient.interpretKey r)
    (hm : keyPolyEqual (mulKey zp zq) (scaleKey (k : ℤ) zr) = true) :
    R7.Core.SpectralCoefficient.interpretKey r =
      R7.Core.SpectralCoefficient.interpretKey p *
      R7.Core.SpectralCoefficient.interpretKey q := by
  have hi := congrArg interpretKey (keyPolyEqual_sound _ _ hm)
  rw [interpretKey_mul, interpretKey_scale, hp, hq, hr] at hi
  have hprod : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) * MvPolynomial.C (dq : ℚ) =
      MvPolynomial.C (k : ℚ) * MvPolynomial.C (dr : ℚ) := by
    simpa only [← map_mul, ← Nat.cast_mul] using congrArg
      (fun n : ℕ => (MvPolynomial.C (n : ℚ) : PolynomialChart.Poly)) hfactor
  have hnonzero : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) *
      MvPolynomial.C (dq : ℚ) ≠ 0 := by simp [hdp, hdq]
  apply mul_left_cancel₀ hnonzero
  calc
    _ = MvPolynomial.C (k : ℚ) * MvPolynomial.C (dr : ℚ) *
        R7.Core.SpectralCoefficient.interpretKey r := by rw [hprod]
    _ = _ := by linear_combination -hi

/-- Addition with a checked common denominator. -/
theorem add_semantic_of_scaled (dp dq dr ap aq ar common : ℕ) (hd : common ≠ 0)
    (hfp : ap * dp = common) (hfq : aq * dq = common) (hfr : ar * dr = common)
    (p q r : R7.Core.SpectralCoefficient.KeyPoly) (zp zq zr : KeyPoly)
    (hp : interpretKey zp = MvPolynomial.C (dp : ℚ) * R7.Core.SpectralCoefficient.interpretKey p)
    (hq : interpretKey zq = MvPolynomial.C (dq : ℚ) * R7.Core.SpectralCoefficient.interpretKey q)
    (hr : interpretKey zr = MvPolynomial.C (dr : ℚ) * R7.Core.SpectralCoefficient.interpretKey r)
    (hi : MvPolynomial.C (ap : ℚ) * interpretKey zp +
        MvPolynomial.C (aq : ℚ) * interpretKey zq =
      MvPolynomial.C (ar : ℚ) * interpretKey zr) :
    R7.Core.SpectralCoefficient.interpretKey r =
      R7.Core.SpectralCoefficient.interpretKey p +
      R7.Core.SpectralCoefficient.interpretKey q := by
  rw [hp, hq, hr] at hi
  have hC (a d : ℕ) (hf : a * d = common) :
      (MvPolynomial.C (a : ℚ) : PolynomialChart.Poly) * MvPolynomial.C (d : ℚ) =
        MvPolynomial.C (common : ℚ) := by
    simpa only [← map_mul, ← Nat.cast_mul] using congrArg
      (fun n : ℕ => (MvPolynomial.C (n : ℚ) : PolynomialChart.Poly)) hf
  have hnonzero : (MvPolynomial.C (common : ℚ) : PolynomialChart.Poly) ≠ 0 := by simp [hd]
  apply mul_left_cancel₀ hnonzero
  calc
    _ = MvPolynomial.C (ar : ℚ) * (MvPolynomial.C (dr : ℚ) *
        R7.Core.SpectralCoefficient.interpretKey r) := by rw [← hC ar dr hfr, mul_assoc]
    _ = _ := hi.symm
    _ = _ := by rw [← mul_assoc, hC ap dp hfp, ← mul_assoc, hC aq dq hfq, mul_add]

/-- Power checking can use any verified integer implementation (including the
symmetric square driver) while leaving the rational theorem statement intact. -/
theorem pow_semantic_of_scaled (dp dr k n : ℕ) (hdp : dp ≠ 0)
    (hfactor : dp ^ n = k * dr)
    (p r : R7.Core.SpectralCoefficient.KeyPoly) (zp zr : KeyPoly)
    (hp : interpretKey zp = MvPolynomial.C (dp : ℚ) * R7.Core.SpectralCoefficient.interpretKey p)
    (hr : interpretKey zr = MvPolynomial.C (dr : ℚ) * R7.Core.SpectralCoefficient.interpretKey r)
    (hi : interpretKey zp ^ n = MvPolynomial.C (k : ℚ) * interpretKey zr) :
    R7.Core.SpectralCoefficient.interpretKey r =
      R7.Core.SpectralCoefficient.interpretKey p ^ n := by
  rw [hp, hr, mul_pow] at hi
  have hprod : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) ^ n =
      MvPolynomial.C (k : ℚ) * MvPolynomial.C (dr : ℚ) := by
    simpa only [← map_pow, ← map_mul, ← Nat.cast_pow, ← Nat.cast_mul] using congrArg
      (fun m : ℕ => (MvPolynomial.C (m : ℚ) : PolynomialChart.Poly)) hfactor
  have hnonzero : (MvPolynomial.C (dp : ℚ) : PolynomialChart.Poly) ^ n ≠ 0 := by
    simp [hdp]
  apply mul_left_cancel₀ hnonzero
  calc
    _ = MvPolynomial.C (k : ℚ) * MvPolynomial.C (dr : ℚ) *
        R7.Core.SpectralCoefficient.interpretKey r := by rw [hprod]
    _ = _ := by linear_combination -hi

end R7.Core.SpectralCoefficient.Kronecker

namespace R7.Core.SpectralCoefficient.Kronecker
open R7.ComputablePolynomial
open Polynomial

/-- Keys for Horner evaluation are derived from the bound exponent functions. -/
def packed (base : ℕ) (p : KeyPoly) : List (ℕ × ℤ) :=
  p.reverse.map (fun a => (encode base a.exp, a.value))

theorem interpret_reverse (p : KeyPoly) : interpretKey p.reverse = interpretKey p := by
  induction p with
  | nil => rfl
  | cons a ps ih =>
    simp only [List.reverse_cons, interpretKey_append, ih, interpretKey]
    abel

theorem substitution_interpret (base : ℕ) (p : KeyPoly) :
    MvPolynomial.eval₂Hom Polynomial.C
      (fun i => (Polynomial.X : Polynomial ℚ)^weight base i) (interpretKey p) =
      (R7.Algebra.Kronecker.polynomial (p.map (fun a => (encode base a.exp, a.value)))).map
        (Int.castRingHom ℚ) := by
  induction p with
  | nil => simp [interpretKey, R7.Algebra.Kronecker.polynomial]
  | cons a ps ih =>
    change MvPolynomial.eval₂Hom Polynomial.C _
      (MvPolynomial.monomial (exponent a.exp) (a.value : ℚ) + interpretKey ps) = _
    rw [map_add, substitution_monomial, ih]
    simp [R7.Algebra.Kronecker.polynomial, exponent]

/-- Check weakly increasing exponents. -/
def orderedFrom : ℕ → List (ℕ × ℤ) → Bool
  | _, [] => true
  | n, (m, _) :: rest => decide (m ≤ n) && orderedFrom m rest

theorem orderedFrom_sound (n : ℕ) (ts : List (ℕ × ℤ))
    (h : orderedFrom n ts = true) : R7.Algebra.SparseHorner.OrderedFrom n ts := by
  induction ts generalizing n with
  | nil => trivial
  | cons a ts ih =>
    have hs := Bool.and_eq_true_iff.mp h
    exact ⟨of_decide_eq_true hs.1, ih a.1 hs.2⟩

def ordered (ts : List (ℕ × ℤ)) : Bool :=
  match ts with
  | [] => true
  | a :: rest => orderedFrom a.1 rest

theorem ordered_sound (ts : List (ℕ × ℤ)) (h : ordered ts = true) :
    ∀ first tail, ts = first :: tail → R7.Algebra.SparseHorner.OrderedFrom first.1 tail := by
  intro first tail he
  rw [he] at h
  exact orderedFrom_sound _ _ h

def candidate (base : ℕ) (p : KeyPoly) : R7.Algebra.Kronecker.Expr :=
  R7.Algebra.IntegerHorner.horner (packed base p)

theorem candidate_substitution (base : ℕ) (p : KeyPoly) (h : ordered (packed base p) = true) :
    (candidate base p).denote.map (Int.castRingHom ℚ) =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun i => (Polynomial.X : Polynomial ℚ)^weight base i) (interpretKey p) := by
  rw [candidate, R7.Algebra.IntegerHorner.denote_horner _ (ordered_sound _ h)]
  rw [← interpret_reverse p, substitution_interpret]
  rfl

/-- A complete rational polynomial identity obtained from a single exact
integer evaluation. Exponent injectivity, coefficient bounds, denominator
binding, homogeneous degrees and Horner order are all explicit hypotheses. -/
theorem identity_of_evaluation (base d denominator : ℕ)
    (hb : 1 < base) (hd : d < base) (hden : denominator ≠ 0)
    (source : R7.ComputablePolynomial.Expr)
    (p : R7.Core.SpectralCoefficient.KeyPoly) (zp : KeyPoly)
    (hbind : interpretKey zp = MvPolynomial.C (denominator : ℚ) *
      R7.Core.SpectralCoefficient.interpretKey p)
    (hsource : source.denote.IsHomogeneous d)
    (hp : (R7.Core.SpectralCoefficient.interpretKey p).IsHomogeneous d)
    (hordered : ordered (packed base zp) = true)
    {B : ℤ}
    (hbound : (R7.Algebra.Kronecker.Expr.mul (.constant denominator)
        (R7.Algebra.Kronecker.clearLCM (weight base) source).numerator).bound +
      (R7.Algebra.Kronecker.Expr.mul
        (.constant (R7.Algebra.Kronecker.clearLCM (weight base) source).denominator)
        (candidate base zp)).bound < B)
    (hpoint : (R7.Algebra.Kronecker.Expr.mul (.constant denominator)
        (R7.Algebra.Kronecker.clearLCM (weight base) source).numerator).evaluateFast B =
      (R7.Algebra.Kronecker.Expr.mul
        (.constant (R7.Algebra.Kronecker.clearLCM (weight base) source).denominator)
        (candidate base zp)).evaluateFast B) :
    R7.Core.SpectralCoefficient.interpretKey p = source.denote := by
  have hu := R7.Algebra.Kronecker.clearLCM_identity_of_evaluation (weight base) source
    (candidate base zp) denominator hbound
      (by simpa only [R7.Algebra.Kronecker.Expr.evaluateFast_correct] using hpoint)
  rw [candidate_substitution base zp hordered, hbind, map_mul, MvPolynomial.eval₂Hom_C] at hu
  rw [R7.Algebra.Kronecker.rationalExpression_correct] at hu
  have hC : (Polynomial.C (denominator : ℚ)) ≠ 0 := by simp [hden]
  have hsubst := mul_left_cancel₀ hC hu
  exact (homogeneous_eq_of_substitution_eq base hb _ _ d hd hsource hp hsubst).symm

end R7.Core.SpectralCoefficient.Kronecker

/-! Integer coefficient views of rational sparse polynomials. -/
namespace R7.Core.SpectralCoefficient.Kronecker.IntegerView
open R7.ComputablePolynomial
open Polynomial

abbrev IntegerPoly := R7.Algebra.IntegerSparse.KeyPoly

/-- Extract the base-32 key and integer numerator. -/
def view (p : R7.Core.SpectralCoefficient.KeyPoly) : IntegerPoly :=
  p.map (fun a => ⟨a.key, a.value.num⟩)

def termCheck (a : R7.Core.SpectralCoefficient.Term) (d : ℕ) : Bool :=
  (a.value.den == 1) && (a.key == expCode a.exp) && (totalExp a.exp == d)

def tableCheck (p : R7.Core.SpectralCoefficient.KeyPoly) (d : ℕ) : Bool :=
  p.all (fun a => termCheck a d)

theorem termCheck_sound (a : R7.Core.SpectralCoefficient.Term) (d : ℕ)
    (h : termCheck a d = true) :
    a.value.den = 1 ∧ a.key = expCode a.exp ∧ totalExp a.exp = d := by
  have hs := Bool.and_eq_true_iff.mp h
  have hk := Bool.and_eq_true_iff.mp hs.1
  exact ⟨by simpa using hk.1, by simpa using hk.2, by simpa using hs.2⟩

theorem tableCheck_sound (p : R7.Core.SpectralCoefficient.KeyPoly) (d : ℕ)
    (h : tableCheck p d = true) :
    ∀ a ∈ p, a.value.den = 1 ∧ a.key = expCode a.exp ∧ totalExp a.exp = d := by
  intro a ha
  exact termCheck_sound a d ((List.all_eq_true.mp h) a ha)

theorem view_correct_of_forall (p : R7.Core.SpectralCoefficient.KeyPoly)
    (h : ∀ a ∈ p, a.value.den = 1 ∧ a.key = expCode a.exp) :
    (R7.Algebra.IntegerSparse.interpretKey (view p)).map (Int.castRingHom ℚ) =
      FullSubstitution.apply (R7.Core.SpectralCoefficient.interpretKey p) := by
  induction p with
  | nil => simp [view, R7.Algebra.IntegerSparse.interpretKey, R7.Core.SpectralCoefficient.interpretKey]
  | cons a ps ih =>
    have ha := h a (by simp)
    have hnum : (a.value.num : ℚ) = a.value := by
      simpa [ha.1] using Rat.num_div_den a.value
    have hcode : FullSubstitution.code (exponent a.exp) = a.key := by
      rw [FullSubstitution.code_eq_expCode]
      simpa [expCode, exponent] using ha.2.symm
    change (Polynomial.monomial a.key a.value.num +
      R7.Algebra.IntegerSparse.interpretKey (view ps)).map _ = _
    rw [Polynomial.map_add, Polynomial.map_monomial,
      R7.Core.SpectralCoefficient.interpretKey, map_add,
      FullSubstitution.apply_monomial, hcode,
      ih (fun b hb => h b (by simp [hb]))]
    change Polynomial.monomial a.key (a.value.num : ℚ) + _ = _
    rw [hnum]

theorem view_correct (p : R7.Core.SpectralCoefficient.KeyPoly) (d : ℕ)
    (h : tableCheck p d = true) :
    (R7.Algebra.IntegerSparse.interpretKey (view p)).map (Int.castRingHom ℚ) =
      FullSubstitution.apply (R7.Core.SpectralCoefficient.interpretKey p) :=
  view_correct_of_forall p (fun a ha => ⟨(tableCheck_sound p d h a ha).1,
    (tableCheck_sound p d h a ha).2.1⟩)

theorem table_homogeneous (p : R7.Core.SpectralCoefficient.KeyPoly) (d : ℕ)
    (h : tableCheck p d = true) :
    (R7.Core.SpectralCoefficient.interpretKey p).IsHomogeneous d :=
  interpret_homogeneous p d (fun a ha => (tableCheck_sound p d h a ha).2.2)

/-- This is the exact rational product theorem used in each substitution group.
All coefficient-integrality, key encoding and support bounds are checked; no
unproved injectivity assumption is delegated to the caller. -/
theorem multiply (p q r : R7.Core.SpectralCoefficient.KeyPoly) (dp dq : ℕ)
    (hd : dp + dq < 32)
    (hp : tableCheck p dp = true) (hq : tableCheck q dq = true)
    (hr : tableCheck r (dp + dq) = true)
    (hm : R7.Algebra.IntegerSparse.keyPolyEqual
      (R7.Algebra.IntegerSparse.mulFusedShort (view p) (view q)) (view r) = true) :
    R7.Core.SpectralCoefficient.interpretKey p * R7.Core.SpectralCoefficient.interpretKey q =
      R7.Core.SpectralCoefficient.interpretKey r := by
  have he := congrArg R7.Algebra.IntegerSparse.interpretKey
    (R7.Algebra.IntegerSparse.keyPolyEqual_sound _ _ hm)
  rw [R7.Algebra.IntegerSparse.interpret_mulFusedShort] at he
  have hi := congrArg (fun t : Polynomial ℤ => t.map (Int.castRingHom ℚ)) he
  dsimp only at hi
  rw [Polynomial.map_mul, view_correct p dp hp, view_correct q dq hq,
    view_correct r (dp + dq) hr] at hi
  apply FullSubstitution.homogeneous_eq _ _ (dp + dq) hd
    ((table_homogeneous p dp hp).mul (table_homogeneous q dq hq))
    (table_homogeneous r (dp + dq) hr)
  simpa only [map_mul] using hi

end R7.Core.SpectralCoefficient.Kronecker.IntegerView
