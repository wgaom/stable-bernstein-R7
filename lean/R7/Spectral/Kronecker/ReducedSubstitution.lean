import R7.Spectral.Kronecker.Core

/-! Three-gap Kronecker substitution on a fixed-u homogeneous slice. -/
namespace R7.Core.SpectralCoefficient.Kronecker.Reduced
open R7.ComputablePolynomial Polynomial
open scoped BigOperators
abbrev Poly := MvPolynomial (Fin 5) ℚ

def FixedU (p : Poly) (j : ℕ) : Prop :=
  ∀ e, MvPolynomial.coeff e p ≠ 0 → e 0 = j

theorem FixedU.add {p q : Poly} {j : ℕ} (hp : FixedU p j) (hq : FixedU q j) :
    FixedU (p+q) j := by
  intro e he
  rw [MvPolynomial.coeff_add] at he
  by_cases hz : MvPolynomial.coeff e p = 0
  · rw [hz, zero_add] at he
    exact hq e he
  · exact hp e hz

theorem FixedU.neg {p : Poly} {j : ℕ} (hp : FixedU p j) : FixedU (-p) j := by
  intro e he
  apply hp e
  simpa only [MvPolynomial.coeff_neg, neg_ne_zero] using he

theorem FixedU.sub {p q : Poly} {j : ℕ} (hp : FixedU p j) (hq : FixedU q j) :
    FixedU (p-q) j := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem FixedU.mul {p q : Poly} {j k : ℕ} (hp : FixedU p j) (hq : FixedU q k) :
    FixedU (p*q) (j+k) := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul] at he
  obtain ⟨⟨a,b⟩, hab, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have ha : MvPolynomial.coeff a p ≠ 0 := left_ne_zero_of_mul hn
  have hb : MvPolynomial.coeff b q ≠ 0 := right_ne_zero_of_mul hn
  have hsum : a+b=e := Finset.mem_antidiagonal.mp hab
  rw [← hsum, Finsupp.add_apply, hp a ha, hq b hb]

theorem FixedU.monomial (e : Fin 5 →₀ ℕ) (c : ℚ) (j : ℕ) (hj : e 0=j) :
    FixedU (MvPolynomial.monomial e c) j := by
  classical
  intro f hf
  rw [MvPolynomial.coeff_monomial] at hf
  split_ifs at hf with h
  · subst f; exact hj
  · exact False.elim (hf rfl)

theorem fixedU_table (p : R7.Core.SpectralCoefficient.KeyPoly) (j : ℕ)
    (h : ∀ a∈p, a.exp 0=j) : FixedU (R7.Core.SpectralCoefficient.interpretKey p) j := by
  induction p with
  | nil => intro e he; exact False.elim (he (MvPolynomial.coeff_zero e))
  | cons a ps ih =>
    apply FixedU.add
    · apply FixedU.monomial
      simpa [exponent] using h a (by simp)
    · exact ih (fun b hb => h b (by simp [hb]))

def code (base : ℕ) (e : Fin 5 → ℕ) : ℕ := Nat.ofDigits base [e 1,e 2,e 3]
def weight (base : ℕ) : Fin 5 → ℕ := ![0,1,base,base^2,0]

/-- The first and last exponents are recovered from fixed u and total degree. -/
theorem code_injective {base j d : ℕ} (hb : 1<base) {e f : Fin 5 → ℕ}
    (he : e 1<base ∧ e 2<base ∧ e 3<base)
    (hf : f 1<base ∧ f 2<base ∧ f 3<base)
    (heu : e 0=j) (hfu : f 0=j)
    (hed : totalExp e=j+d) (hfd : totalExp f=j+d)
    (h : code base e=code base f) : e=f := by
  have hl : [e 1,e 2,e 3]=[f 1,f 2,f 3] :=
    Nat.ofDigits_inj_of_len_eq hb rfl
      (by simp only [List.mem_cons]; aesop)
      (by simp only [List.mem_cons]; aesop) h
  simp only [List.cons.injEq, and_true] at hl
  rcases hl with ⟨h1,h2,h3⟩
  simp only [totalExp] at hed hfd
  funext i
  fin_cases i <;> simp_all
  omega

noncomputable def apply (base : ℕ) : Poly →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => (Polynomial.X : Polynomial ℚ)^weight base i)

theorem apply_monomial (base : ℕ) (e : Fin 5 →₀ ℕ) (c : ℚ) :
    apply base (MvPolynomial.monomial e c)=Polynomial.monomial (code base e) c := by
  rw [apply, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype]
  · simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    have hh : (∑ i : Fin 5, weight base i*e i)=code base e := by
      simp [weight, code, Nat.ofDigits, Fin.sum_univ_succ]
      ring
    rw [hh, C_mul_X_pow_eq_monomial]
  · intro i; simp

theorem apply_eq_pack (base : ℕ) (p : Poly) :
    apply base p=∑ e∈p.support, Polynomial.monomial (code base e) (MvPolynomial.coeff e p) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [map_sum, apply_monomial]

theorem zero_of_apply_zero (base j d : ℕ) (hb : 1<base) (hd : d<base)
    (p : Poly) (hp : p.IsHomogeneous (j+d)) (hu : FixedU p j)
    (hz : apply base p=0) : p=0 := by
  classical
  have hdegree (e : Fin 5 →₀ ℕ) (he : e∈p.support) : totalExp e=j+d := by
    have hh := hp.degree_eq_sum_deg_support he
    rw [finsupp_sum] at hh
    exact hh.symm
  have hu' (e : Fin 5 →₀ ℕ) (he : e∈p.support) : e 0=j :=
    hu e (MvPolynomial.mem_support_iff.mp he)
  have hcoords (e : Fin 5 →₀ ℕ) (he : e∈p.support) :
      e 1<base ∧ e 2<base ∧ e 3<base := by
    have hh := hdegree e he
    have h0 := hu' e he
    simp only [totalExp] at hh
    omega
  have hi : Set.InjOn (fun e : Fin 5 →₀ ℕ => code base e) (↑p.support : Set _) := by
    intro e he f hf hh
    apply DFunLike.ext
    intro i
    exact congrFun (code_injective hb (hcoords e he) (hcoords f hf)
      (hu' e he) (hu' f hf) (hdegree e he) (hdegree f hf) hh) i
  ext e
  by_cases he : e∈p.support
  · have hh := congrArg (fun q : Polynomial ℚ => q.coeff (code base e)) hz
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

theorem eq_of_apply_eq (base j d : ℕ) (hb : 1<base) (hd : d<base)
    (p q : Poly) (hp : p.IsHomogeneous (j+d)) (hq : q.IsHomogeneous (j+d))
    (hpu : FixedU p j) (hqu : FixedU q j) (he : apply base p=apply base q) : p=q := by
  apply sub_eq_zero.mp
  apply zero_of_apply_zero base j d hb hd (p-q) (hp.sub hq) (hpu.sub hqu)
  simpa only [map_sub, sub_eq_zero] using he

end R7.Core.SpectralCoefficient.Kronecker.Reduced
