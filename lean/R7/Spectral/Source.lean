import R7.Spectral.Polynomial
import R7.Algebra.Covariance
import R7.Spectral.Endpoint
import R7.Spectral.Coordinates.Chart
import R7.Spectral.Coordinates.Symmetry

noncomputable section
namespace R7.Core.SpectralSource
open scoped BigOperators

theorem nHom_normalized (l : Spectrum) (hl : Normalized l) (j : Fin 6) :
 SpectralPolynomial.nHom l j = nVector (terminalParameters) l j := by
 unfold terminalParameters
 unfold SpectralPolynomial.nHom nVector
 have ht : SpectralPolynomial.theta l=1 := hl.2
 rw [ht]
 norm_num [SpectralPolynomial.third,SpectralPolynomial.fourth,moment]
 ring

theorem vHom_normalized (l : Spectrum) (hl : Normalized l) (j : Fin 6) :
 SpectralPolynomial.vHom l j = vVector (terminalParameters) l 0 j := by
 unfold terminalParameters
 unfold SpectralPolynomial.vHom vVector
 have ht : SpectralPolynomial.theta l=1 := hl.2
 rw [ht]
 norm_num [SpectralPolynomial.third,SpectralPolynomial.fourth,moment]

theorem baseHom_normalized (l : Spectrum) (hl : Normalized l) (σ : ℝ) :
 SpectralPolynomial.baseHom σ l = baseL (terminalParameters) l 0 σ := by
 unfold terminalParameters
 unfold SpectralPolynomial.baseHom baseL
 have ht : SpectralPolynomial.theta l=1 := hl.2
 rw [ht]
 norm_num [SpectralPolynomial.third,SpectralPolynomial.fourth,moment]
 ring

theorem covariance_zero (u v : Spectrum) :
 SpectralPolynomial.covariance u v = Covariance.covariance 0 u v := by
 have hw : ∀ j, (SpectralPolynomial.weight j : ℝ)=Covariance.weights 0 j := by
  intro j; by_cases h : j=0 <;> simp [SpectralPolynomial.weight,Covariance.weights,h]
 simp only [SpectralPolynomial.covariance,Covariance.covariance,hw]

theorem denominator_positive (l : Spectrum) (hl : Normalized l) :
 0 < SpectralPolynomial.denominator l := by
 have ht : SpectralPolynomial.theta l=1 := hl.2
 have hi := Covariance.normalized_coordinate_bound l hl 0
 unfold SpectralPolynomial.denominator SpectralPolynomial.denominatorFactor
 rw [ht]
 norm_num
 nlinarith

theorem cleared_identity (l : Spectrum) (hl : Normalized l)
 (R : BasisMatrix) (hR : IsTraceFreeOrthonormalBasis R) (σ a₀ ρ : ℝ) :
 SpectralPolynomial.constant σ a₀ l+ρ*SpectralPolynomial.linear σ l+ρ^2*SpectralPolynomial.quadratic l =
 SpectralPolynomial.denominator l*(Endpoint.scalar l 0 R σ ρ-a₀-(ρ+ρ^2)/100000000) := by
 have ht : SpectralPolynomial.theta l=1 := hl.2
 have hv : SpectralPolynomial.vHom l = vVector (terminalParameters) l 0 := by
  funext j; exact vHom_normalized l hl j
 have hn : SpectralPolynomial.nHom l = nVector (terminalParameters) l := by
  funext j; exact nHom_normalized l hl j
 have hδ : (138/25:ℝ)-(151/25)*(1/3+(l 0)^2/2) ≠ 0 := by
  have hi := Covariance.normalized_coordinate_bound l hl 0
  have : (0:ℝ)<138/25-(151/25)*(1/3+(l 0)^2/2) := by nlinarith
  exact ne_of_gt this
 have hLoss := Covariance.inversePair_covariance l 0 R hl hR (vVector (terminalParameters) l 0)
 unfold SpectralPolynomial.constant SpectralPolynomial.linear SpectralPolynomial.quadratic SpectralPolynomial.quartic SpectralPolynomial.denominator SpectralPolynomial.denominatorFactor
 rw [ht,baseHom_normalized l hl σ,hv,hn]
 simp only [covariance_zero]
 unfold Endpoint.scalar Endpoint.loss
 rw [hLoss]
 have hδ' : (526:ℝ)-(l 0)^2*453 ≠ 0 := by
  have hi := Covariance.normalized_coordinate_bound l hl 0
  have : (0:ℝ)<526-(l 0)^2*453 := by nlinarith
  exact ne_of_gt this
 norm_num
 field_simp [hδ,hδ']
 ring_nf
 field_simp [hδ']
 ring

def ChartCertificate (σ a₀ : ℚ) : Prop :=
 ∀ (z : ℝ) (g : Fin 4 → ℝ) (ρ : ℝ), (∀ j, 0 ≤ g j) → 0 ≤ ρ →
  0 ≤ MvPolynomial.aeval (Fin.cons z g) (SpectralPolynomial.constantE σ a₀).denote
    +ρ*MvPolynomial.aeval (Fin.cons z g) (SpectralPolynomial.linearE σ).denote
    +ρ^2*MvPolynomial.aeval (Fin.cons z g) SpectralPolynomial.quadraticE.denote

theorem scalar_bound_of_numerator (l : Spectrum) (hl : Normalized l)
 (R : BasisMatrix) (hR : IsTraceFreeOrthonormalBasis R) (σ a₀ ρ : ℝ)
 (hnum : 0 ≤ SpectralPolynomial.constant σ a₀ l+ρ*SpectralPolynomial.linear σ l
   +ρ^2*SpectralPolynomial.quadratic l) :
 a₀+(ρ+ρ^2)/100000000 ≤ Endpoint.scalar l 0 R σ ρ := by
 rw [cleared_identity l hl R hR σ a₀ ρ] at hnum
 have hp := denominator_positive l hl
 have hgap : 0 ≤ Endpoint.scalar l 0 R σ ρ-a₀-(ρ+ρ^2)/100000000 :=
  (mul_nonneg_iff_of_pos_left hp).mp hnum
 linarith

theorem quartic_bound_of_chart (σ a₀ : ℚ) (hcert : ChartCertificate σ a₀)
 (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
 (hl : Normalized l) (hR : IsTraceFreeOrthonormalBasis R) (y : ℝ) :
 (a₀:ℝ)+(y^2+y^4)/100000000 ≤ R7.quartic (terminalParameters) l i R σ y := by
 obtain ⟨e,he,hsort⟩ := SpectralChart.sorted_representative l i
 let v := reindexSpectrum e l
 have hv : Normalized v := (normalized_reindex e l).2 hl
 let g : Fin 4 → ℝ := ![(v 2-v 1)/5,(v 3-v 2)/5,(v 4-v 3)/5,(v 5-v 4)/5]
 let z : ℝ := v 0/5
 have hg : ∀ j, 0 ≤ g j := by
  have h12 : v 1 ≤ v 2 := hsort (by decide : (0:Fin 5)≤1)
  have h23 : v 2 ≤ v 3 := hsort (by decide : (1:Fin 5)≤2)
  have h34 : v 3 ≤ v 4 := hsort (by decide : (2:Fin 5)≤3)
  have h45 : v 4 ≤ v 5 := hsort (by decide : (3:Fin 5)≤4)
  intro j; fin_cases j <;> simp [g] <;> linarith
 have hraw : PolynomialChart.spectrumAt (Fin.cons z g)=v := by
  change SpectralChart.kappa z g=v
  exact SpectralChart.chart_inverse v hv.1
 have hn := hcert z g (y^2) hg (sq_nonneg y)
 rw [SpectralPolynomial.Expr.eval_denote (Fin.cons z g) (SpectralPolynomial.constantE σ a₀),
   SpectralPolynomial.Expr.eval_denote (Fin.cons z g) (SpectralPolynomial.linearE σ),
   SpectralPolynomial.Expr.eval_denote (Fin.cons z g) SpectralPolynomial.quadraticE,
   SpectralPolynomial.eval_constant,SpectralPolynomial.eval_linear,
   SpectralPolynomial.eval_quadratic,hraw] at hn
 have hbR : IsTraceFreeOrthonormalBasis (reindexBasis e R) :=
  (basis_reindex e R).2 hR
 have hs := scalar_bound_of_numerator v hv (reindexBasis e R) hbR σ a₀ (y^2) hn
 have hq : (a₀:ℝ)+(y^2+y^4)/100000000 ≤
   R7.quartic (terminalParameters) v 0 (reindexBasis e R) σ y := by
  rw [Endpoint.quartic_eq_scalar]
  convert hs using 1; ring
 have heq : R7.quartic (terminalParameters) v 0 (reindexBasis e R) σ y =
  R7.quartic (terminalParameters) l i R σ y := by
  simpa only [one_mul,reindexSpectrum,v] using
   quartic_signed_reindex_zero 1 (Or.inl rfl) e (terminalParameters) l i he R σ y
 rw [heq] at hq
 exact hq

theorem interpolation_identity (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
 (a b t y : ℝ) :
 R7.quartic (terminalParameters) l i R ((1-t)*a+t*b) y =
  (1-t)*R7.quartic (terminalParameters) l i R a y
   +t*R7.quartic (terminalParameters) l i R b y
   +t*(1-t)*(b-a)^2*(1/5+(5/4)*y^2) := by
 simp only [Endpoint.quartic_eq_scalar,Endpoint.scalar]
 unfold baseL
 unfold terminalParameters
 norm_num
 ring

theorem interval_bound_of_charts
 (hentry : ChartCertificate (12481/5000) (1/1000000000))
 (hcritical : ChartCertificate (5/2) 0)
 (σ : ℝ) (hσl : 12481/5000 ≤ σ) (hσr : σ ≤ 5/2)
 (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
 (hl : Normalized l) (hR : IsTraceFreeOrthonormalBasis R) (y : ℝ) :
 (5/2-σ)/3800000+(y^2+y^4)/100000000 ≤
  R7.quartic (terminalParameters) l i R σ y := by
 let t : ℝ := (σ-12481/5000)/(19/5000)
 have ht0 : 0 ≤ t := by dsimp [t]; linarith
 have ht1 : t ≤ 1 := by dsimp [t]; linarith
 have hmixσ : (1-t)*(12481/5000:ℝ)+t*(5/2)=σ := by dsimp [t]; ring
 have hi := interpolation_identity l i R (12481/5000) (5/2) t y
 rw [hmixσ] at hi
 have hp : 0 ≤ t*(1-t)*((5/2:ℝ)-12481/5000)^2*(1/5+(5/4)*y^2) := by
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg _)
  · positivity
 have ha := quartic_bound_of_chart (12481/5000) (1/1000000000) hentry l i R hl hR y
 have hb := quartic_bound_of_chart (5/2) 0 hcritical l i R hl hR y
 norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,zero_add] at ha hb
 have hsum := add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1))
   (mul_le_mul_of_nonneg_left hb ht0)
 have hmargin : (1-t)*((1:ℝ)/1000000000+(y^2+y^4)/100000000)
   +t*((y^2+y^4)/100000000) =
   (5/2-σ)/3800000+(y^2+y^4)/100000000 := by dsimp [t]; ring
 rw [hmargin] at hsum
 rw [hi]
 exact hsum.trans (le_add_of_nonneg_right hp)

theorem scalar_interval_of_charts
 (hentry : ChartCertificate (12481/5000) (1/1000000000))
 (hcritical : ChartCertificate (5/2) 0)
 (σ : ℝ) (hσl : 12481/5000 ≤ σ) (hσr : σ ≤ 5/2)
 (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
 (hl : Normalized l) (hR : IsTraceFreeOrthonormalBasis R)
 (ρ : ℝ) (hρ : 0 ≤ ρ) :
 (5/2-σ)/3800000+(ρ+ρ^2)/100000000 ≤ Endpoint.scalar l i R σ ρ := by
 apply Endpoint.scalar_bound_of_quartic_bound l i R σ ρ ((5/2-σ)/3800000) hρ
 intro y hy
 exact interval_bound_of_charts hentry hcritical σ hσl hσr l i R hl hR y

theorem quadratic_nonneg_of_quartic (l : Spectrum) (ht : (∑ j, l j)=0)
 (hq : 0 ≤ SpectralPolynomial.quartic l) : 0 ≤ SpectralPolynomial.quadratic l := by
 have hθ : 0 ≤ SpectralPolynomial.theta l := Finset.sum_nonneg fun j _ => sq_nonneg (l j)
 have hi := Covariance.tracefree_coordinate_bound l ht 0
 have hD : 0 ≤ SpectralPolynomial.denominatorFactor l := by
  unfold SpectralPolynomial.denominatorFactor
  change (0:ℝ) ≤ (2*(151/25)/3-13/25)*(∑ j, (l j)^2)-((151/25)/2)*(l 0)^2
  change (0:ℝ) ≤ ∑ j, (l j)^2 at hθ
  nlinarith
 unfold SpectralPolynomial.quadratic
 exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD) hθ) hq

theorem quadratic_nonneg_of_quartic_nonneg (z : ℝ) (g : Fin 4 → ℝ)
 (hq : 0 ≤ MvPolynomial.aeval (Fin.cons z g) SpectralPolynomial.quarticE.denote) :
 0 ≤ MvPolynomial.aeval (Fin.cons z g) SpectralPolynomial.quadraticE.denote := by
 rw [SpectralPolynomial.Expr.eval_denote,SpectralPolynomial.eval_quartic] at hq
 rw [SpectralPolynomial.Expr.eval_denote,SpectralPolynomial.eval_quadratic]
 apply quadratic_nonneg_of_quartic _ _ hq
 change (∑ j, SpectralChart.kappa z g j)=0
 exact SpectralChart.kappa_trace z g

theorem critical_constant_eval (z : ℝ) (g : Fin 4 → ℝ) :
 MvPolynomial.aeval (Fin.cons z g) (SpectralPolynomial.constantE (5/2) 0).denote = 0 := by
 rw [SpectralPolynomial.Expr.eval_denote,SpectralPolynomial.eval_constant]
 unfold SpectralPolynomial.constant
 norm_num

end R7.Core.SpectralSource
