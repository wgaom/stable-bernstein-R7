import R7.Spectral.Kronecker.ReducedSubstitution
import R7.Spectral.Kronecker.Core
import R7.Algebra.IntegerSparsePolynomial
import R7.Spectral.Kronecker.ReducedSort

namespace R7.Core.SpectralCoefficient.Kronecker.Reduced
open R7.ComputablePolynomial Polynomial
abbrev KExpr := R7.Algebra.Kronecker.Expr
abbrev Terms := R7.Algebra.Kronecker.Terms

def tableCheck (p : R7.Core.SpectralCoefficient.KeyPoly) (j d : ℕ) : Bool :=
  p.all (fun a => (a.value.den == 1) && (a.exp 0 == j) && (totalExp a.exp == d))

theorem tableCheck_sound (p : R7.Core.SpectralCoefficient.KeyPoly) (j d : ℕ)
    (h : tableCheck p j d = true) :
    ∀ a∈p, a.value.den=1 ∧ a.exp 0=j ∧ totalExp a.exp=d := by
  intro a ha
  have hs := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp h) a ha)
  have ht := Bool.and_eq_true_iff.mp hs.1
  exact ⟨by simpa using ht.1, by simpa using ht.2, by simpa using hs.2⟩

/-- Extend the integer and total-degree checks with the fixed-u degree. -/
theorem tableCheck_of_integer_view (p : R7.Core.SpectralCoefficient.KeyPoly) (j d : ℕ)
    (h : R7.Core.SpectralCoefficient.Kronecker.IntegerView.tableCheck p d=true)
    (hu : p.all (fun a => a.exp 0 == j)=true) : tableCheck p j d=true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hi := R7.Core.SpectralCoefficient.Kronecker.IntegerView.tableCheck_sound p d h a ha
  have hx : a.exp 0=j := by simpa using (List.all_eq_true.mp hu) a ha
  simp only [Bool.and_eq_true_iff,beq_iff_eq]
  exact ⟨⟨hi.1,hx⟩,hi.2.2⟩

def raw (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) : Terms :=
  p.map (fun a => (code base a.exp, a.value.num))

def asKeys (ts : Terms) : R7.Algebra.IntegerSparse.KeyPoly :=
  ts.map (fun a => ⟨a.1,a.2⟩)

def fromKeys (ts : R7.Algebra.IntegerSparse.KeyPoly) : Terms :=
  ts.map (fun a => (a.key,a.value))

def packed (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) : Terms :=
  Sort.sort (raw base p)

def candidate (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) : KExpr :=
  R7.Algebra.IntegerHorner.horner (packed base p)

theorem polynomial_perm {p q : Terms} (h : p.Perm q) :
    R7.Algebra.Kronecker.polynomial p=R7.Algebra.Kronecker.polynomial q := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [R7.Algebra.Kronecker.polynomial, ih]
  | swap a b l => simp only [R7.Algebra.Kronecker.polynomial]; abel
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem asKeys_correct (ts : Terms) : R7.Algebra.IntegerSparse.interpretKey (asKeys ts)=
    R7.Algebra.Kronecker.polynomial ts := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [asKeys, List.map_cons, R7.Algebra.IntegerSparse.interpretKey,
      R7.Algebra.Kronecker.polynomial, ← ih]

theorem fromKeys_correct (ts : R7.Algebra.IntegerSparse.KeyPoly) :
    R7.Algebra.Kronecker.polynomial (fromKeys ts)=R7.Algebra.IntegerSparse.interpretKey ts := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [fromKeys, List.map_cons, R7.Algebra.IntegerSparse.interpretKey,
      R7.Algebra.Kronecker.polynomial, ← ih]

theorem packed_correct (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Algebra.Kronecker.polynomial (packed base p)=R7.Algebra.Kronecker.polynomial (raw base p) := by
  exact polynomial_perm (Sort.sort_perm _)

theorem ordered_of_sorted (ts : Terms) (h : Sort.Sorted ts) :
    R7.Core.SpectralCoefficient.Kronecker.ordered ts=true := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
    cases ts with
    | nil => rfl
    | cons b rest =>
      have hh := List.pairwise_cons.mp h
      change ((decide (b.1≤a.1)) && R7.Core.SpectralCoefficient.Kronecker.orderedFrom b.1 rest)=true
      apply Bool.and_eq_true_iff.mpr
      exact ⟨by simpa using hh.1 b (by simp), by simpa [R7.Core.SpectralCoefficient.Kronecker.ordered] using ih hh.2⟩

theorem packed_ordered (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly) :
    R7.Core.SpectralCoefficient.Kronecker.ordered (packed base p)=true :=
  ordered_of_sorted _ (Sort.sort_sorted _)

theorem raw_correct (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (h : ∀ a∈p, a.value.den=1) :
    (R7.Algebra.Kronecker.polynomial (raw base p)).map (Int.castRingHom ℚ) =
      apply base (R7.Core.SpectralCoefficient.interpretKey p) := by
  induction p with
  | nil => simp [raw, R7.Algebra.Kronecker.polynomial, R7.Core.SpectralCoefficient.interpretKey]
  | cons a ps ih =>
    have ha := h a (by simp)
    have hn : (a.value.num : ℚ)=a.value := by
      simpa [ha] using Rat.num_div_den a.value
    change (Polynomial.monomial (code base a.exp) a.value.num +
      R7.Algebra.Kronecker.polynomial (raw base ps)).map _ = _
    rw [Polynomial.map_add, Polynomial.map_monomial,
      R7.Core.SpectralCoefficient.interpretKey, map_add, apply_monomial,
      ih (fun b hb => h b (by simp [hb]))]
    simpa [exponent] using congrArg
      (fun c : ℚ => Polynomial.monomial (code base a.exp) c +
        apply base (R7.Core.SpectralCoefficient.interpretKey ps)) hn

theorem candidate_correct (base j d : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (h : tableCheck p j d=true)
    (ho : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base p)=true) :
    (candidate base p).denote.map (Int.castRingHom ℚ)=
      apply base (R7.Core.SpectralCoefficient.interpretKey p) := by
  rw [candidate, R7.Algebra.IntegerHorner.denote_horner _ (R7.Core.SpectralCoefficient.Kronecker.ordered_sound _ ho)]
  rw [packed_correct]
  exact raw_correct base p (fun a ha => (tableCheck_sound p j d h a ha).1)

theorem candidate_raw (base : ℕ) (p : R7.Core.SpectralCoefficient.KeyPoly)
    (ho : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base p)=true) :
    (candidate base p).denote=R7.Algebra.Kronecker.polynomial (raw base p) := by
  rw [candidate, R7.Algebra.IntegerHorner.denote_horner _
    (R7.Core.SpectralCoefficient.Kronecker.ordered_sound _ ho), packed_correct]

theorem point_identity_raw (base : ℕ) (p q r : R7.Core.SpectralCoefficient.KeyPoly)
    (hop : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base p)=true)
    (hoq : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base q)=true)
    (hor : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base r)=true)
    {B : ℤ}
    (hbound : R7.Algebra.Kronecker.mass (raw base p)*R7.Algebra.Kronecker.mass (raw base q)+
      R7.Algebra.Kronecker.mass (raw base r)<B)
    (hpoint : (candidate base p).evaluateFast B*(candidate base q).evaluateFast B=
      (candidate base r).evaluateFast B) :
    R7.Algebra.Kronecker.polynomial (raw base p)*R7.Algebra.Kronecker.polynomial (raw base q)=
      R7.Algebra.Kronecker.polynomial (raw base r) := by
  have hB : 0<B := lt_of_le_of_lt
    (add_nonneg (mul_nonneg (R7.Algebra.Kronecker.mass_nonneg _) (R7.Algebra.Kronecker.mass_nonneg _))
      (R7.Algebra.Kronecker.mass_nonneg _)) hbound
  apply R7.Algebra.Kronecker.eq_of_eval_eq hB
  · intro n
    have ha := R7.Algebra.Kronecker.coefficient_abs_le_mass
      (R7.Algebra.Kronecker.times (raw base p) (raw base q)) n
    rw [R7.Algebra.Kronecker.polynomial_times, R7.Algebra.Kronecker.mass_times] at ha
    exact lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add ha
      (R7.Algebra.Kronecker.coefficient_abs_le_mass (raw base r) n))) hbound
  · rw [← candidate_raw base p hop, ← candidate_raw base q hoq, ← candidate_raw base r hor]
    simpa only [Polynomial.eval_mul, R7.Algebra.Kronecker.Expr.evaluate_correct,
      ← R7.Algebra.Kronecker.Expr.evaluateFast_correct] using hpoint

/-- Product identity from bounded evaluation on a fixed-u homogeneous slice. -/
theorem multiply (base j d : ℕ) (p q r : R7.Core.SpectralCoefficient.KeyPoly)
    (hb : 1<base) (hd : d<base)
    (hp : tableCheck p j d=true) (hq : tableCheck q 0 j=true)
    (hr : tableCheck r j (d+j)=true)
    (hop : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base p)=true)
    (hoq : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base q)=true)
    (hor : R7.Core.SpectralCoefficient.Kronecker.ordered (packed base r)=true)
    {B : ℤ}
    (hbound : R7.Algebra.Kronecker.mass (raw base p)*R7.Algebra.Kronecker.mass (raw base q)+
      R7.Algebra.Kronecker.mass (raw base r)<B)
    (hpoint : (candidate base p).evaluateFast B*(candidate base q).evaluateFast B=
      (candidate base r).evaluateFast B) :
    R7.Core.SpectralCoefficient.interpretKey p * R7.Core.SpectralCoefficient.interpretKey q =
      R7.Core.SpectralCoefficient.interpretKey r := by
  have hi := point_identity_raw base p q r hop hoq hor hbound hpoint
  have hm := congrArg (fun t : Polynomial ℤ => t.map (Int.castRingHom ℚ)) hi
  dsimp only at hm
  rw [Polynomial.map_mul,
    raw_correct base p (fun a ha => (tableCheck_sound p j d hp a ha).1),
    raw_correct base q (fun a ha => (tableCheck_sound q 0 j hq a ha).1),
    raw_correct base r (fun a ha => (tableCheck_sound r j (d+j) hr a ha).1)] at hm
  have ph := interpret_homogeneous p d (fun a ha => (tableCheck_sound p j d hp a ha).2.2)
  have qh := interpret_homogeneous q j (fun a ha => (tableCheck_sound q 0 j hq a ha).2.2)
  have rh := interpret_homogeneous r (d+j) (fun a ha => (tableCheck_sound r j (d+j) hr a ha).2.2)
  have pu := fixedU_table p j (fun a ha => (tableCheck_sound p j d hp a ha).2.1)
  have qu := fixedU_table q 0 (fun a ha => (tableCheck_sound q 0 j hq a ha).2.1)
  have ru := fixedU_table r j (fun a ha => (tableCheck_sound r j (d+j) hr a ha).2.1)
  apply eq_of_apply_eq base j d hb hd _ _
    (by simpa only [Nat.add_comm] using ph.mul qh)
    (by simpa only [Nat.add_comm] using rh)
    (by simpa only [Nat.add_zero] using pu.mul qu) ru
  simpa only [map_mul] using hm

end R7.Core.SpectralCoefficient.Kronecker.Reduced
