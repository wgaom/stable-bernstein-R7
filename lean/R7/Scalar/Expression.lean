import R7.Definitions
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace R7.Core

noncomputable section

def spectralFactor (r : ℝ) : ℝ := 1/3+r/2

def j (p : Parameters) (y : ℝ) : ℝ := (p.m22 : ℝ)*y^2+2*p.m12*y+p.m11

def beta (p : Parameters) (y : ℝ) : ℝ := Paper.detM p / j p y

def m11tilde (p : Parameters) (y : ℝ) : ℝ := p.m11-y^2*beta p y

def m12tilde (p : Parameters) (y : ℝ) : ℝ := p.m12+y*beta p y

def alphaInvSq (p : Parameters) (r y : ℝ) : ℝ :=
  spectralFactor r / ((p.m22 : ℝ)-p.c6-((p.m22 : ℝ)-beta p y)*spectralFactor r)

def etaSq (p : Parameters) (r y : ℝ) : ℝ :=
  6/5-m11tilde p y-(m12tilde p y)^2*alphaInvSq p r y

def B0 (p : Parameters) (sigma r y : ℝ) : ℝ :=
  sigma*(5-2*sigma)/10-(p.m11 : ℝ)/4+(p.c6 : ℝ)*y^4+2*p.m12*y^3+
  ((p.c8 : ℝ)*(1-sigma/2)-(p.m12 : ℝ)*(3-sigma)/2)*y+
  y^2*beta p y*(1-sigma/2)^2+
  y^2*((2*(p.c3 : ℝ)*(1-sigma/5)-1)*r-(p.c3 : ℝ)*(1-2*sigma/5)+p.m11-
    (p.c6 : ℝ)/2*(3-sigma)*(sigma-2)-(p.m22 : ℝ)/4*(3-sigma)^2-
    (p.c7 : ℝ)/2*(sigma-2))

def B1 (p : Parameters) (sigma y : ℝ) : ℝ :=
  (p.c7 : ℝ)*y+p.c8-p.m12+2*y*beta p y*(1-sigma/2)

def B2 (p : Parameters) (sigma y : ℝ) : ℝ :=
  p.c4+((p.c8 : ℝ)-(p.m12 : ℝ)*(3-sigma))*y-2*y^2*beta p y*(1-sigma/2)

def scalarCore (p : Parameters) (sigma r Lambda y : ℝ) : ℝ :=
  B0 p sigma r y-(B1 p sigma y)^2*alphaInvSq p r y/4-
  (p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4-
  (6/5*(p.c3 : ℝ)*(r-1/6)*y^2+B2 p sigma y+
    m12tilde p y*B1 p sigma y*alphaInvSq p r y)^2/(4*etaSq p r y)

def scalarF (p : Parameters) (sigma q y : ℝ) : ℝ :=
  scalarCore p sigma (q^2) (Paper.Lambda q) y

def alphaSq (p : Parameters) (r y : ℝ) : ℝ :=
  ((p.m22 : ℝ)-p.c6)/spectralFactor r-p.m22+beta p y

def s22 (p : Parameters) (y : ℝ) : ℝ := 6/5-m11tilde p y

def s12 (p : Parameters) (y : ℝ) : ℝ := -m12tilde p y

def su (p : Parameters) (sigma y : ℝ) : ℝ := B1 p sigma y

def sz (p : Parameters) (sigma r y : ℝ) : ℝ :=
  6/5*(p.c3 : ℝ)*(r-1/6)*y^2+B2 p sigma y

def detS (p : Parameters) (r y : ℝ) : ℝ :=
  alphaSq p r y*s22 p y-(s12 p y)^2

def H (p : Parameters) (r y : ℝ) : ℝ :=
  ((p.m22 : ℝ)-p.c6-(p.m22 : ℝ)*spectralFactor r)*j p y+Paper.detM p*spectralFactor r

def K (p : Parameters) (y : ℝ) : ℝ :=
  (6/5-(p.m11 : ℝ))*j p y+Paper.detM p*y^2

def TT (p : Parameters) (y : ℝ) : ℝ :=
  (p.m12 : ℝ)*j p y+Paper.detM p*y

def X (p : Parameters) (sigma y : ℝ) : ℝ :=
  ((p.c7 : ℝ)*y+p.c8-p.m12)*j p y+2*Paper.detM p*(1-sigma/2)*y

def W (p : Parameters) (sigma r y : ℝ) : ℝ :=
  (6/5*(p.c3 : ℝ)*(r-1/6)*y^2+p.c4+
    ((p.c8 : ℝ)-(p.m12 : ℝ)*(3-sigma))*y)*j p y-
  2*Paper.detM p*(1-sigma/2)*y^2

def Dstar (p : Parameters) (r y : ℝ) : ℝ :=
  (((p.m22 : ℝ)-p.c6-(p.m22 : ℝ)*spectralFactor r)*(6/5-(p.m11 : ℝ))-
    spectralFactor r*(p.m12 : ℝ)^2)*j p y+
  Paper.detM p*(((p.m22 : ℝ)-p.c6-(p.m22 : ℝ)*spectralFactor r)*y^2+
    (6/5-(p.m11 : ℝ))*spectralFactor r-2*spectralFactor r*(p.m12 : ℝ)*y)

theorem Dstar_mul_j (p : Parameters) (r y : ℝ) :
    Dstar p r y*j p y = K p y*H p r y-spectralFactor r*(TT p y)^2 := by
  unfold Dstar K H TT j Paper.detM
  ring

theorem alphaSq_as_fraction (p : Parameters) (r y : ℝ)
    (hd : spectralFactor r ≠ 0) (hj : j p y ≠ 0) :
    alphaSq p r y = H p r y/(spectralFactor r*j p y) := by
  unfold alphaSq H beta
  field_simp

theorem s22_as_fraction (p : Parameters) (y : ℝ) (hj : j p y ≠ 0) :
    s22 p y = K p y/j p y := by
  unfold s22 K m11tilde beta
  field_simp
  ring

theorem s12_as_fraction (p : Parameters) (y : ℝ) (hj : j p y ≠ 0) :
    s12 p y = -TT p y/j p y := by
  unfold s12 TT m12tilde beta
  field_simp

theorem su_as_fraction (p : Parameters) (sigma y : ℝ) (hj : j p y ≠ 0) :
    su p sigma y = X p sigma y/j p y := by
  unfold su X B1 beta
  field_simp

theorem sz_as_fraction (p : Parameters) (sigma r y : ℝ) (hj : j p y ≠ 0) :
    sz p sigma r y = W p sigma r y/j p y := by
  unfold sz W B2 beta
  field_simp
  ring

def rationalDen (x : ℝ) : ℝ := 1+6*x^2

def rationalR (x : ℝ) : ℝ := 5*x^2/rationalDen x

def rationalLambda (x : ℝ) : ℝ :=
  8/15-(12*x-1)^2/(20*(rationalDen x)^2)

theorem rationalDen_pos (x : ℝ) : 0 < rationalDen x := by
  unfold rationalDen
  positivity

theorem rational_envelope (x : ℝ) :
    207/125*(rationalR x)^2-33/25*rationalR x+29/60+
      6/5*x/(rationalDen x)^2 = rationalLambda x := by
  have hd := ne_of_gt (rationalDen_pos x)
  unfold rationalR rationalLambda
  field_simp
  unfold rationalDen; ring

theorem spectral_chart (q : ℝ) (hq : 0 ≤ q) (hmax : q^2 < 5/6) :
    ∃ x : ℝ, 0 ≤ x ∧ q^2 = rationalR x ∧ Paper.Lambda q = rationalLambda x := by
  let z := Real.sqrt (5-6*q^2)
  have hzarg : 0 < 5-6*q^2 := by linarith
  have hz : 0 < z := Real.sqrt_pos.2 hzarg
  have hzs : z^2 = 5-6*q^2 := Real.sq_sqrt (le_of_lt hzarg)
  let x := q/z
  have hx : 0 ≤ x := div_nonneg hq (le_of_lt hz)
  have hxz : x*z = q := div_mul_cancel₀ q (ne_of_gt hz)
  have hAz : rationalDen x*z^2 = 5 := by
    unfold rationalDen
    nlinarith [sq_nonneg (x*z-q)]
  have hA := ne_of_gt (rationalDen_pos x)
  have hr : q^2 = rationalR x := by
    unfold rationalR
    apply (eq_div_iff hA).2
    calc
      q^2*rationalDen x = (x*z)^2*rationalDen x := by rw [hxz]
      _ = x^2*(rationalDen x*z^2) := by ring
      _ = 5*x^2 := by rw [hAz]; ring
  have hrad : q*z^3 = 25*x/(rationalDen x)^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hA)).2
    calc
      q*z^3*(rationalDen x)^2 = (x*z)*z^3*(rationalDen x)^2 := by rw [hxz]
      _ = x*(rationalDen x*z^2)^2 := by ring
      _ = 25*x := by rw [hAz]; ring
  refine ⟨x, hx, hr, ?_⟩
  unfold Paper.Lambda
  change 207/125*q^4-33/25*q^2+29/60+6/125*q*z^3 = rationalLambda x
  have hfour : q^4 = (rationalR x)^2 := by rw [← hr]; ring
  rw [hfour, hr]
  calc
    _ = 207/125*(rationalR x)^2-33/25*rationalR x+29/60+
        6/125*(q*z^3) := by ring
    _ = 207/125*(rationalR x)^2-33/25*rationalR x+29/60+
        6/5*x/(rationalDen x)^2 := by rw [hrad]; ring
    _ = rationalLambda x := rational_envelope x

theorem combine_quadratic_fractions (t d h u z : ℝ) (ht : t ≠ 0) (hd : d ≠ 0) :
    -u^2*t/4-(z+h*u*t)^2/(4*d) =
    -((d+h^2*t)*u^2+2*h*u*z+(1/t)*z^2)/(4*(d/t)) := by
  field_simp
  ring

theorem j_pos (p : Parameters) (hp : MatrixSigns p) (y : ℝ) (hy : 0 ≤ y) :
    0 < j p y := by
  rcases hp with ⟨hd, hc, hk, _, ht, _, _⟩
  have hd' : 0 < (p.m22 : ℝ) := by exact_mod_cast (show 0 < p.m22 by linarith)
  have hk' : 0 < (p.m11 : ℝ) := by exact_mod_cast hk
  have ht' : 0 ≤ (p.m12 : ℝ) := by exact_mod_cast ht
  unfold j
  positivity

theorem beta_pos (p : Parameters) (hp : MatrixSigns p) (y : ℝ) (hy : 0 ≤ y) :
    0 < beta p y := by
  have hdet : 0 < Paper.detM p := by
    unfold Paper.detM
    exact_mod_cast hp.2.2.2.2.2.1
  exact div_pos hdet (j_pos p hp y hy)

theorem denominator_pos (p : Parameters) (hp : MatrixSigns p)
    (r y : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 5/6) (hy : 0 ≤ y) :
    0 < alphaSq p r y ∧ 0 < detS p r y ∧ 0 < alphaInvSq p r y ∧ 0 < etaSq p r y := by
  rcases hp with ⟨hd, hc, hk, hku, ht, hdet, hbase⟩
  have hd' : 4*(p.c6 : ℝ) < p.m22 := by exact_mod_cast hd
  have hc' : 0 < (p.c6 : ℝ) := by exact_mod_cast hc
  have hk' : (p.m11 : ℝ) < 4/5 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hku
    norm_num at h ⊢
    exact h
  have hb' : (p.m12 : ℝ)^2 < ((p.m22 : ℝ)-4*p.c6)/3*(6/5-(p.m11 : ℝ)) := by
    have h := (Rat.cast_lt (K := ℝ)).2 hbase
    push_cast at h
    norm_num at h ⊢
    exact h
  have hD : 0 < spectralFactor r := by unfold spectralFactor; linarith
  have hDu : spectralFactor r ≤ 3/4 := by unfold spectralFactor; linarith
  let a := ((p.m22 : ℝ)-p.c6)/spectralFactor r-p.m22
  let b : ℝ := 6/5-p.m11
  have hb : 0 < b := by dsimp [b]; linarith
  have hal : ((p.m22 : ℝ)-4*p.c6)/3 ≤ a := by
    dsimp [a]
    have hdiv : 4*((p.m22 : ℝ)-p.c6)/3 ≤ ((p.m22 : ℝ)-p.c6)/spectralFactor r := by
      apply (le_div_iff₀ hD).2
      nlinarith
    linarith
  have ha : 0 < a := by linarith
  have hab : 0 < a*b-(p.m12 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_right hal (le_of_lt hb)
    dsimp [b] at *
    linarith
  have hquad : 0 < a*y^2+b-2*(p.m12 : ℝ)*y := by
    have hs := sq_nonneg (a*y-(p.m12 : ℝ))
    have hpq : 0 < a*(a*y^2+b-2*(p.m12 : ℝ)*y) := by nlinarith
    exact pos_of_mul_pos_right hpq (le_of_lt ha)
  have hpfull : MatrixSigns p := ⟨hd,hc,hk,hku,ht,hdet,hbase⟩
  have hbeta := beta_pos p hpfull y hy
  have hs11 : 0 < alphaSq p r y := by
    change 0 < a+beta p y
    linarith
  have hdetS : 0 < detS p r y := by
    have hid : detS p r y = a*b-(p.m12 : ℝ)^2+
        beta p y*(a*y^2+b-2*(p.m12 : ℝ)*y) := by
      unfold detS alphaSq s22 s12 m11tilde m12tilde
      dsimp [a,b]
      ring
    rw [hid]
    positivity
  have hTinv : alphaInvSq p r y = 1/alphaSq p r y := by
    unfold alphaInvSq alphaSq
    field_simp
    ring
  have hT : 0 < alphaInvSq p r y := by rw [hTinv]; positivity
  have hsmall : etaSq p r y = detS p r y*alphaInvSq p r y := by
    simp only [hTinv]
    unfold etaSq detS s22 s12
    simp only [hTinv]
    have hsne := ne_of_gt hs11
    field_simp

  exact ⟨hs11,hdetS,hT,by rw [hsmall]; positivity⟩

def scalarCombined (p : Parameters) (sigma r Lambda y : ℝ) : ℝ :=
  B0 p sigma r y-(p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4-
  (s22 p y*(su p sigma y)^2-2*s12 p y*su p sigma y*sz p sigma r y+
    alphaSq p r y*(sz p sigma r y)^2)/(4*detS p r y)

theorem alphaInvSq_eq_inv_alphaSq (p : Parameters) (r y : ℝ) (hd : spectralFactor r ≠ 0) :
    alphaInvSq p r y = 1/alphaSq p r y := by
  unfold alphaInvSq alphaSq
  field_simp
  ring

theorem scalarCore_eq_combined (p : Parameters) (sigma r Lambda y : ℝ)
    (hd : spectralFactor r ≠ 0) (hs : alphaSq p r y ≠ 0) (hdet : detS p r y ≠ 0) :
    scalarCore p sigma r Lambda y = scalarCombined p sigma r Lambda y := by
  have hT := alphaInvSq_eq_inv_alphaSq p r y hd
  have ht : alphaInvSq p r y ≠ 0 := by rw [hT]; exact one_div_ne_zero hs
  have hsmall : etaSq p r y = detS p r y*alphaInvSq p r y := by
    unfold etaSq detS s22 s12
    simp only [hT]
    field_simp

  have hsmallnz : etaSq p r y ≠ 0 := by
    rw [hsmall]
    exact mul_ne_zero hdet ht
  have hs22 : s22 p y = etaSq p r y+(m12tilde p y)^2*alphaInvSq p r y := by
    unfold s22 etaSq
    ring
  have hsinv : alphaSq p r y = 1/alphaInvSq p r y := by rw [hT]; simp
  have hdetrel : detS p r y = etaSq p r y/alphaInvSq p r y := by
    apply (eq_div_iff ht).2
    exact hsmall.symm
  have hc := combine_quadratic_fractions (alphaInvSq p r y) (etaSq p r y)
    (m12tilde p y) (B1 p sigma y) (sz p sigma r y) ht hsmallnz
  calc
    scalarCore p sigma r Lambda y =
        B0 p sigma r y-(p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4+
        (-(B1 p sigma y)^2*alphaInvSq p r y/4-
          (sz p sigma r y+m12tilde p y*B1 p sigma y*alphaInvSq p r y)^2/(4*etaSq p r y)) := by
      unfold scalarCore sz
      ring
    _ = B0 p sigma r y-(p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4+
        (-((etaSq p r y+(m12tilde p y)^2*alphaInvSq p r y)*(B1 p sigma y)^2+
          2*m12tilde p y*B1 p sigma y*sz p sigma r y+
          (1/alphaInvSq p r y)*(sz p sigma r y)^2)/(4*(etaSq p r y/alphaInvSq p r y))) := by rw [hc]
    _ = scalarCombined p sigma r Lambda y := by
      unfold scalarCombined su s12
      rw [← hs22, ← hsinv, ← hdetrel]
      ring

theorem detS_as_fraction (p : Parameters) (r y : ℝ)
    (hd : spectralFactor r ≠ 0) (hj : j p y ≠ 0) :
    detS p r y = Dstar p r y/(spectralFactor r*j p y) := by
  unfold detS
  rw [alphaSq_as_fraction p r y hd hj, s22_as_fraction p y hj,
    s12_as_fraction p y hj]
  calc
    _ = (K p y*H p r y-spectralFactor r*(TT p y)^2)/(spectralFactor r*(j p y)^2) := by
      field_simp

    _ = (Dstar p r y*j p y)/(spectralFactor r*(j p y)^2) := by rw [Dstar_mul_j]
    _ = Dstar p r y/(spectralFactor r*j p y) := by field_simp

theorem Dstar_pos (p : Parameters) (hp : MatrixSigns p)
    (r y : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 5/6) (hy : 0 ≤ y) :
    0 < Dstar p r y := by
  have hd : 0 < spectralFactor r := by unfold spectralFactor; linarith
  have hj := j_pos p hp y hy
  have hs := (denominator_pos p hp r y hr hrmax hy).2.1
  rw [detS_as_fraction p r y (ne_of_gt hd) (ne_of_gt hj)] at hs
  exact (div_pos_iff_of_pos_right (mul_pos hd hj)).1 hs

def basePolynomial (p : Parameters) (sigma r Lambda y m : ℝ) : ℝ :=
  sigma*(5-2*sigma)/10-(p.m11 : ℝ)/4+(p.c6 : ℝ)*y^4+2*p.m12*y^3+
  ((p.c8 : ℝ)*(1-sigma/2)-(p.m12 : ℝ)*(3-sigma)/2)*y+
  y^2*((2*(p.c3 : ℝ)*(1-sigma/5)-1)*r-(p.c3 : ℝ)*(1-2*sigma/5)+p.m11-
    (p.c6 : ℝ)/2*(3-sigma)*(sigma-2)-(p.m22 : ℝ)/4*(3-sigma)^2-
    (p.c7 : ℝ)/2*(sigma-2))-
  (p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4-m*(1+y^2+y^4)

def rawNumerator (p : Parameters) (sigma r Lambda y m : ℝ) : ℝ :=
  4*(j p y)^2*Dstar p r y*basePolynomial p sigma r Lambda y m+
  4*Paper.detM p*(1-sigma/2)^2*y^2*j p y*Dstar p r y-
  spectralFactor r*K p y*(X p sigma y)^2-
  2*spectralFactor r*TT p y*X p sigma y*W p sigma r y-
  H p r y*(W p sigma r y)^2

theorem scalarCore_raw_identity (p : Parameters) (sigma r Lambda y m : ℝ)
    (hd : spectralFactor r ≠ 0) (hj : j p y ≠ 0) (hs : alphaSq p r y ≠ 0)
    (hdet : detS p r y ≠ 0) (hstar : Dstar p r y ≠ 0) :
    scalarCore p sigma r Lambda y-m*(1+y^2+y^4) =
      rawNumerator p sigma r Lambda y m/(4*Dstar p r y*(j p y)^2) := by
  rw [scalarCore_eq_combined p sigma r Lambda y hd hs hdet]
  have hb : B0 p sigma r y-(p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4-
      m*(1+y^2+y^4) = basePolynomial p sigma r Lambda y m+
      y^2*beta p y*(1-sigma/2)^2 := by
    unfold B0 basePolynomial
    ring
  unfold scalarCombined
  rw [alphaSq_as_fraction p r y hd hj,s22_as_fraction p y hj,
    s12_as_fraction p y hj,su_as_fraction p sigma y hj,
    sz_as_fraction p sigma r y hj,detS_as_fraction p r y hd hj]
  have hrew : B0 p sigma r y = basePolynomial p sigma r Lambda y m+
      y^2*beta p y*(1-sigma/2)^2+
      (p.c3 : ℝ)^2/4*(Lambda-6/5*(r-1/6)^2)*y^4+m*(1+y^2+y^4) := by linarith [hb]
  rw [hrew]
  unfold rawNumerator beta
  field_simp
  ring

theorem scalarCore_lower_of_raw_nonneg (p : Parameters) (hp : MatrixSigns p)
    (sigma r Lambda y m : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 5/6) (hy : 0 ≤ y)
    (hraw : 0 ≤ rawNumerator p sigma r Lambda y m) :
    m*(1+y^2+y^4) ≤ scalarCore p sigma r Lambda y := by
  have hd : 0 < spectralFactor r := by unfold spectralFactor; linarith
  have hj := j_pos p hp y hy
  have hpos := denominator_pos p hp r y hr hrmax hy
  have hstar := Dstar_pos p hp r y hr hrmax hy
  have hid := scalarCore_raw_identity p sigma r Lambda y m
    (ne_of_gt hd) (ne_of_gt hj) (ne_of_gt hpos.1) (ne_of_gt hpos.2.1) (ne_of_gt hstar)
  have hdiv : 0 ≤ rawNumerator p sigma r Lambda y m /
      (4*Dstar p r y*(j p y)^2) := div_nonneg hraw (by positivity)
  linarith [hid]

theorem scalarF_lower_of_chart_raw_nonneg (p : Parameters) (hp : MatrixSigns p)
    (sigma q y m : ℝ) (hq : 0 ≤ q) (hqmax : q^2 < 5/6) (hy : 0 ≤ y)
    (hraw : ∀ x : ℝ, 0 ≤ x →
      0 ≤ rawNumerator p sigma (rationalR x) (rationalLambda x) y m) :
    m*(1+y^2+y^4) ≤ scalarF p sigma q y := by
  obtain ⟨x,hx,hr,hL⟩ := spectral_chart q hq hqmax
  unfold scalarF
  have hb := scalarCore_lower_of_raw_nonneg p hp sigma (q^2) (Paper.Lambda q) y m
    (sq_nonneg q) (le_of_lt hqmax) hy
  apply hb
  rw [hr,hL]
  exact hraw x hx

theorem scalarF_continuousAt (p : Parameters) (hp : MatrixSigns p)
    (sigma y q : ℝ) (hy : 0 ≤ y) (hqmax : q^2 ≤ 5/6) :
    ContinuousAt (fun z : ℝ => scalarF p sigma z y) q := by
  have hpos := denominator_pos p hp (q^2) y (sq_nonneg q) hqmax hy
  have ht : alphaInvSq p (q^2) y ≠ 0 := ne_of_gt hpos.2.2.1
  have hsmall : etaSq p (q^2) y ≠ 0 := ne_of_gt hpos.2.2.2
  have hfour : (4 : ℝ) ≠ 0 := by norm_num
  have hden4 : 4*etaSq p (q^2) y ≠ 0 := mul_ne_zero hfour hsmall
  have htd : (p.m22 : ℝ)-p.c6-((p.m22 : ℝ)-beta p y)*spectralFactor (q^2) ≠ 0 := by
    exact (div_ne_zero_iff.1 ht).2
  have hTcont : ContinuousAt (fun z : ℝ => alphaInvSq p (z^2) y) q := by
    unfold alphaInvSq
    apply ContinuousAt.div
    · unfold spectralFactor; fun_prop
    · unfold spectralFactor; fun_prop
    · exact htd
  have hsmallcont : ContinuousAt (fun z : ℝ => etaSq p (z^2) y) q := by
    unfold etaSq
    fun_prop
  unfold scalarF scalarCore
  have hB0 : ContinuousAt (fun z : ℝ => B0 p sigma (z^2) y) q := by
    unfold B0
    fun_prop
  have henv : ContinuousAt Paper.Lambda q := by
    unfold Paper.Lambda
    fun_prop
  fun_prop (disch := assumption)

theorem scalarF_lower_of_chart_raw_nonneg_closed (p : Parameters) (hp : MatrixSigns p)
    (sigma q y m : ℝ) (hq : 0 ≤ q) (hqmax : q^2 ≤ 5/6) (hy : 0 ≤ y)
    (hraw : ∀ x : ℝ, 0 ≤ x →
      0 ≤ rawNumerator p sigma (rationalR x) (rationalLambda x) y m) :
    m*(1+y^2+y^4) ≤ scalarF p sigma q y := by
  by_cases hstrict : q^2 < 5/6
  · exact scalarF_lower_of_chart_raw_nonneg p hp sigma q y m hq hstrict hy hraw
  have hqpos : 0 < q := by nlinarith
  have hcont := scalarF_continuousAt p hp sigma y q hy hqmax
  have hlim : Filter.Tendsto (fun z : ℝ => scalarF p sigma z y)
      (nhdsWithin q (Set.Iio q)) (nhds (scalarF p sigma q y)) :=
    hcont.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (s := Set.Iio q) (Ioi_mem_nhds hqpos)] with z hz hzpos
  apply scalarF_lower_of_chart_raw_nonneg p hp sigma z y m (le_of_lt hzpos) _ hy hraw
  change z < q at hz
  change 0 < z at hzpos
  have hm := mul_pos (sub_pos.mpr hz) (add_pos hqpos hzpos)
  nlinarith

end
end R7.Core
