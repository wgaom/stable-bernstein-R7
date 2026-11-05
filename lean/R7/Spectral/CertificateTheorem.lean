import R7.Certificates.Spectral.Coefficients.EntryAGrouped
import R7.Certificates.Spectral.Coefficients.EntryLGrouped
import R7.Certificates.Spectral.Coefficients.EntryQGrouped
import R7.Certificates.Spectral.Coefficients.CriticalLGrouped
import R7.Certificates.Spectral.Coefficients.CriticalQ8Grouped
import R7.Spectral.Source

namespace R7.Core.SpectralCertificateTheorem
open scoped BigOperators
open R7.ComputablePolynomial R7.Core.SpectralGrouped
open R7.Core.SpectralSlices R7.Core.SpectralCoefficient
open R7.Core.SpectralPolynomial R7.Core.SpectralSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem grouped_source_eval (G : Groups) (j : ℕ) (data : KeyPoly)
 (a : Expr) (scale : ℚ)
 (hgroup : normalizeKey (flattenGrouped G j)=data)
 (hsource : interpretKey data=(.mul (.rat scale) (substitute a) : Expr).denote)
 (u : ℝ) (g : Fin 4 → ℝ) :
 MvPolynomial.aeval (point u g) (interpretKey (flattenGrouped G j)) =
 (scale : ℝ)*Expr.eval (point (u*∑ j, g j) g) a := by
 have hi : interpretKey (flattenGrouped G j)=
     (.mul (.rat scale) (substitute a) : Expr).denote := by
   calc
    _ = interpretKey (normalizeKey (flattenGrouped G j)) := (interpret_normalizeKey _).symm
    _ = interpretKey data := by rw [hgroup]
    _ = _ := hsource
 rw [hi, Expr.eval_denote]
 simp only [Expr.eval,eval_substitute]
 congr 1
 congr 1
 funext i
 refine Fin.cases ?_ (fun j => ?_) i
 · change u*(g 0+g 1+g 2+g 3)=u*∑ j, g j
   simp only [Fin.sum_univ_succ]
   change u*(g 0+g 1+g 2+g 3)=u*(g 0+(g 1+(g 2+(g 3+0))))
   ring
 · simp [slicePoint,point]

theorem continuous_axis (P : PolynomialChart.Poly) (z : ℝ) :
 Continuous (fun t : ℝ => MvPolynomial.aeval (point z (fun _ => t)) P) := by
 simp only [MvPolynomial.aeval_def,MvPolynomial.eval₂_eq']
 apply continuous_finset_sum
 intro e _
 apply Continuous.mul continuous_const
 apply continuous_finset_prod
 intro i _
 apply Continuous.pow
 fin_cases i <;> simp [point] <;> fun_prop

theorem closed_gap_nonneg (f : ℝ → (Fin 4 → ℝ) → ℝ)
 (hcont : ∀ z, Continuous (fun t : ℝ => f z (fun _ => t)))
 (hpos : ∀ z g, (∀ j, 0 ≤ g j) → (0 < ∑ j, g j) → 0 ≤ f z g)
 (z : ℝ) (g : Fin 4 → ℝ) (hg : ∀ j, 0 ≤ g j) : 0 ≤ f z g := by
 have hH : 0 ≤ ∑ j, g j := Finset.sum_nonneg fun j _ => hg j
 rcases eq_or_lt_of_le hH with hzero|hpositive
 · have hgeq : g=0 := by
     funext j
     have hj : g j ≤ ∑ j, g j := Finset.single_le_sum (fun k _ => hg k) (Finset.mem_univ j)
     have : g j=0 := by have := hg j; linarith
     exact this
   rw [hgeq]
   have hc : IsClosed {t : ℝ | 0 ≤ f z (fun _=>t)} :=
     isClosed_le continuous_const (hcont z)
   have hs : Set.Ioi (0 : ℝ) ⊆ {t : ℝ | 0 ≤ f z (fun _=>t)} := by
     intro t ht
     change 0<t at ht
     exact hpos z (fun _=>t) (fun _=>le_of_lt ht) (by
       simp only [Fin.sum_univ_succ]; change 0<t+(t+(t+(t+0))); linarith)
   have hcl : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by simp [closure_Ioi]
   have hh : 0 ≤ f z (fun _=>0) := (hc.closure_subset_iff.mpr hs) hcl
   simpa using hh
 · exact hpos z g hg hpositive

theorem entry_chart_of_sources
 (hA : interpretKey entryAData=(.mul (.rat 11250000)
    (substitute (constantE (12481/5000) (1/1000000000))) : Expr).denote)
 (hL : interpretKey entryLData=(.mul (.rat 11250000)
    (substitute (linearE (12481/5000))) : Expr).denote)
 (hQ : interpretKey entryQData=(.mul (.rat 11250000)
    (substitute quadraticE) : Expr).denote) :
 ChartCertificate (12481/5000) (1/1000000000) := by
 intro z g ρ hg hρ
 let f : ℝ → (Fin 4 → ℝ) → ℝ := fun z g =>
   MvPolynomial.aeval (point z g) (constantE (12481/5000) (1/1000000000)).denote +
   ρ*MvPolynomial.aeval (point z g) (linearE (12481/5000)).denote +
   ρ^2*MvPolynomial.aeval (point z g) quadraticE.denote
 change 0 ≤ f z g
 apply closed_gap_nonneg f _ _ z g hg
 · intro z
   exact ((continuous_axis _ z).add (continuous_const.mul (continuous_axis _ z))).add
     (continuous_const.mul (continuous_axis _ z))
 · intro z g hg hH
   let u := z/(∑ j, g j)
   have hu : u*(∑ j,g j)=z := div_mul_cancel₀ z (ne_of_gt hH)
   have hn := group_sum_nonneg entryGroups u ρ g hg
     (fun row hr => le_of_lt (entryGroups_positive row hr u ρ hρ))
   rw [← reconstruct_three entryGroups entryGroups_short] at hn
   rw [grouped_source_eval _ 0 entryAData _ 11250000 groupedEntryA_checked hA,
     grouped_source_eval _ 1 entryLData _ 11250000 groupedEntryL_checked hL,
     grouped_source_eval _ 2 entryQData _ 11250000 groupedEntryQ_checked hQ, hu] at hn
   simp only [← Expr.eval_denote] at hn
   change 0 ≤ f z g
   dsimp [f]
   norm_num only [Rat.cast_ofNat] at hn
   nlinarith

theorem single_family_nonneg (G : Groups)
 (hshort : ∀ row ∈ G, ∀ a ∈ row.2, a.length ≤ 3)
 (hpositive : ∀ row ∈ G, ∀ u y : ℝ, 0 ≤ y → 0 < Bivariate.eval row.2 u y)
 (data : KeyPoly) (a : Expr) (scale : ℚ) (hscale : 0<scale)
 (hgroup : normalizeKey (flattenGrouped G 0)=data)
 (hsource : interpretKey data=(.mul (.rat scale) (substitute a) : Expr).denote)
 (z : ℝ) (g : Fin 4 → ℝ) (hg : ∀ j, 0 ≤ g j) :
 0 ≤ MvPolynomial.aeval (point z g) a.denote := by
 apply closed_gap_nonneg (fun z g=>MvPolynomial.aeval (point z g) a.denote)
   (continuous_axis a.denote) _ z g hg
 intro z g hg hH
 let u := z/(∑ j,g j)
 have hu : u*(∑ j,g j)=z := div_mul_cancel₀ z (ne_of_gt hH)
 have hn := group_sum_nonneg G u 0 g hg
   (fun row hr => le_of_lt (hpositive row hr u 0 le_rfl))
 have hi := reconstruct_three G hshort u 0 g
 simp only [zero_mul,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hi
 rw [← hi,grouped_source_eval G 0 data a scale hgroup hsource,hu] at hn
 rw [← Expr.eval_denote] at hn
 exact nonneg_of_mul_nonneg_right hn (by exact_mod_cast hscale)

theorem critical_chart_of_sources
 (hL : interpretKey criticalLData=(.mul (.rat 2250000)
    (substitute (linearE (5/2))) : Expr).denote)
 (hQ : interpretKey criticalQ8Data=(.mul (.rat 60000)
    (substitute quarticE) : Expr).denote) : ChartCertificate (5/2) 0 := by
 intro z g ρ hg hρ
 have hLnon := single_family_nonneg criticalLGroups criticalLGroups_short
   criticalLGroups_positive criticalLData (linearE (5/2)) 2250000 (by norm_num)
   groupedCriticalL_checked hL z g hg
 have hQnon := single_family_nonneg criticalQ8Groups criticalQ8Groups_short
   criticalQ8Groups_positive criticalQ8Data quarticE 60000 (by norm_num)
   groupedCriticalQ8_checked hQ z g hg
 have hquadratic := quadratic_nonneg_of_quartic_nonneg z g hQnon
 rw [critical_constant_eval]
 exact add_nonneg (by simpa using mul_nonneg hρ hLnon)
   (mul_nonneg (sq_nonneg ρ) hquadratic)

end R7.Core.SpectralCertificateTheorem
