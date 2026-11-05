import R7.Definitions
import R7.Algebra.Covariance

noncomputable section
namespace R7.QuadraticMinimum
open scoped BigOperators

private theorem weighted_cauchy (w u z : Fin 6 → ℝ) (hw : ∀ j, 0 < w j) :
 (∑ j, u j*z j)^2 ≤ (∑ j, z j^2/w j)*(∑ j, w j*u j^2) := by
 apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
 · intro j _; exact div_nonneg (sq_nonneg _) (hw j).le
 · intro j _; exact mul_nonneg (hw j).le (sq_nonneg _)
 · intro j _; field_simp [ne_of_gt (hw j)]

private theorem rank_one_minimum (w u v : Fin 6 → ℝ) (a b : ℝ)
 (hw : ∀ j, 0 < w j) (ha : 0 < a) (hb : 0 ≤ b)
 (hd : 0 < a-b*(∑ j, w j*u j^2))
 (hu : ∑ j, w j*u j = 0) (hv : ∑ j, w j*v j = 0) :
 let m := -(1/(4*a))*((∑ j, w j*v j^2)+
   b/(a-b*(∑ j, w j*u j^2))*(∑ j, w j*u j*v j)^2)
 (∀ z : Fin 6 → ℝ, m ≤ a*(∑ j, z j^2/w j)-b*(∑ j, u j*z j)^2+∑ j, v j*z j) ∧
 (∃ z : Fin 6 → ℝ, (∑ j, z j)=0 ∧
   a*(∑ j, z j^2/w j)-b*(∑ j, u j*z j)^2+∑ j, v j*z j=m) := by
 dsimp only
 let U := ∑ j, w j*u j^2
 let K := ∑ j, w j*u j*v j
 let d := a-b*U
 let z₀ : Fin 6 → ℝ := fun j => -w j*(v j+b/d*K*u j)/(2*a)
 have ha0 : a ≠ 0 := ne_of_gt ha
 have hd0 : d ≠ 0 := ne_of_gt hd
 have ht : (∑ j, u j*z₀ j) = -K/(2*d) := by
  have he : (∑ j, u j*z₀ j) = -(K+b/d*K*U)/(2*a) := by
   simp only [z₀,K,U,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
   ring
  rw [he]
  have hd0' : a-b*U ≠ 0 := hd0
  dsimp only [d]
  field_simp [ha0,hd0']
  ring
 have hs (j : Fin 6) : 2*a*z₀ j/w j-2*b*u j*(∑ k, u k*z₀ k)+v j=0 := by
  rw [ht]
  dsimp only [z₀]
  field_simp [ha0,hd0,ne_of_gt (hw j)]
  ring
 have hz : (∑ j, z₀ j)=0 := by
  have he : (∑ j, z₀ j) = -((∑ j, w j*v j)+b/d*K*(∑ j, w j*u j))/(2*a) := by
   simp only [z₀,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
   ring
  rw [he,hu,hv]; ring
 have hlin : (∑ j, v j*z₀ j) = -((∑ j, w j*v j^2)+b/d*K^2)/(2*a) := by
  simp only [z₀,K,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring
 have hstat : 2*(a*(∑ j, z₀ j^2/w j)-b*(∑ j, u j*z₀ j)^2)+∑ j, v j*z₀ j=0 := by
  have he := Finset.sum_eq_zero (s:=Finset.univ) (fun j _ => mul_eq_zero_of_left (hs j) (z₀ j))
  simp only [add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib] at he
  have h1 : (∑ j, 2*a*z₀ j/w j*z₀ j)=2*a*(∑ j, z₀ j^2/w j) := by
   rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : (∑ j, 2*b*u j*(∑ k, u k*z₀ k)*z₀ j)=2*b*(∑ j, u j*z₀ j)^2 := by
   simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
   ring
  rw [h1,h2] at he; linarith
 have hvalue : a*(∑ j, z₀ j^2/w j)-b*(∑ j, u j*z₀ j)^2+∑ j, v j*z₀ j =
   -(1/(4*a))*((∑ j, w j*v j^2)+b/d*K^2) := by
  rw [hlin] at hstat ⊢
  have he : -((∑ j, w j*v j^2)+b/d*K^2)/(2*a)/2 =
    -(1/(4*a))*((∑ j, w j*v j^2)+b/d*K^2) := by ring
  linarith
 have hq (z : Fin 6 → ℝ) : 0 ≤ a*(∑ j, z j^2/w j)-b*(∑ j, u j*z j)^2 := by
  have hc := weighted_cauchy w u z hw
  have hn : 0 ≤ ∑ j, z j^2/w j := Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
  have hm := mul_nonneg (le_of_lt hd) hn
  have hb' := mul_le_mul_of_nonneg_left hc hb
  dsimp [U] at *
  nlinarith
 have hlower (z : Fin 6 → ℝ) :
   a*(∑ j, z₀ j^2/w j)-b*(∑ j, u j*z₀ j)^2+∑ j, v j*z₀ j ≤
   a*(∑ j, z j^2/w j)-b*(∑ j, u j*z j)^2+∑ j, v j*z j := by
  have hn := hq (fun j => z j-z₀ j)
  have hc := Finset.sum_eq_zero (s:=Finset.univ)
    (fun j _ => mul_eq_zero_of_left (hs j) (z j-z₀ j))
  have hex : (a*(∑ j, z j^2/w j)-b*(∑ j, u j*z j)^2+∑ j, v j*z j) -
     (a*(∑ j, z₀ j^2/w j)-b*(∑ j, u j*z₀ j)^2+∑ j, v j*z₀ j) =
     (a*(∑ j, (z j-z₀ j)^2/w j)-b*(∑ j, u j*(z j-z₀ j))^2)+
     ∑ j, (2*a*z₀ j/w j-2*b*u j*(∑ k, u k*z₀ k)+v j)*(z j-z₀ j) := by
   simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
   ring
  rw [hc,add_zero] at hex
  linarith
 constructor
 · intro z; rw [←hvalue]; exact hlower z
 · exact ⟨z₀,hz,hvalue⟩

open R7.Paper
open R7.Core.Covariance (weights)

def D (l : Fin 6 → ℝ) (i : Fin 6) : ℝ := c5*(2/3-(l i)^2/2)-c6

def evaluatedMinimum (l : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
 -(1/(4*(c5-c6)))*((∑ j, weights i j*(V l i j)^2)-
 (3/8)*(∑ j, weights i j*V l i j)^2+
 c5/D l i*(∑ j, weights i j*V l i j*(l j-l i/4))^2)

def objective (l : Fin 6 → ℝ) (i : Fin 6) (z : Fin 6 → ℝ) : ℝ :=
 (c5-c6)*(z i^2+3*(∑ j ∈ Finset.univ.erase i, z j^2))
 -c5*(∑ j, l j*z j)^2+∑ j, V l i j*z j

theorem attains (l : Fin 6 → ℝ) (i : Fin 6)
 (htrace : ∑ j, l j=0) (hnorm : ∑ j, l j^2=1) :
 (∀ z : Fin 6 → ℝ, (∑ j, z j)=0 → evaluatedMinimum l i ≤ objective l i z) ∧
 (∃ z : Fin 6 → ℝ, (∑ j, z j)=0 ∧ objective l i z=evaluatedMinimum l i) := by
 let u : Fin 6 → ℝ := fun j => l j-l i/4
 let m : ℝ := (3/8)*(∑ j, weights i j*V l i j)
 let v : Fin 6 → ℝ := fun j => V l i j-m
 have hw (j : Fin 6) : 0 < weights i j := by unfold weights; split <;> norm_num
 have hwSum : (∑ j, weights i j) = 8/3 := Core.Covariance.weights_sum i
 have hwl : (∑ j, weights i j*l j)=(2/3)*l i := by
  simpa [htrace] using Core.Covariance.weighted_sum i l
 have hwll : (∑ j, weights i j*l j^2)=1/3+(2/3)*(l i)^2 := by
  have h := Core.Covariance.weighted_sum i (fun j => l j^2)
  rw [hnorm] at h
  simpa [Core.Covariance.weights,weights] using h
 have hu : (∑ j, weights i j*u j)=0 := by
  have he : (∑ j, weights i j*u j)=(∑ j, weights i j*l j)-(l i/4)*(∑ j, weights i j) := by
   simp only [u,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
  rw [he,hwl,hwSum]; ring
 have hv : (∑ j, weights i j*v j)=0 := by
  have he : (∑ j, weights i j*v j)=(∑ j, weights i j*V l i j)-m*(∑ j, weights i j) := by
   simp only [v,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
  rw [he,hwSum]; dsimp [m]; ring
 have hU : (∑ j, weights i j*u j^2)=1/3+(l i)^2/2 := by
  have he : (∑ j, weights i j*u j^2)=(∑ j, weights i j*l j^2)-
    2*(l i/4)*(∑ j, weights i j*l j)+(l i/4)^2*(∑ j, weights i j) := by
   simp only [u,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
  rw [he,hwll,hwl,hwSum]; ring
 have hv2 : (∑ j, weights i j*v j^2)=(∑ j, weights i j*(V l i j)^2)-
   (3/8)*(∑ j, weights i j*V l i j)^2 := by
  have he : (∑ j, weights i j*v j^2)=(∑ j, weights i j*(V l i j)^2)-
    2*m*(∑ j, weights i j*V l i j)+m^2*(∑ j, weights i j) := by
   simp only [v,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
  rw [he,hwSum]; dsimp [m]; ring
 have hK : (∑ j, weights i j*u j*v j) = ∑ j, weights i j*V l i j*(l j-l i/4) := by
  have he : (∑ j, weights i j*u j*v j)=(∑ j, weights i j*V l i j*u j)-m*(∑ j, weights i j*u j) := by
   simp only [v,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
  rw [he,hu]; simp only [mul_zero,sub_zero]; rfl
 have hd : 0 < (c5-c6)-c5*(∑ j, weights i j*u j^2) := by
  rw [hU]
  have hb := Core.Covariance.normalized_coordinate_bound l ⟨htrace,hnorm⟩ i
  norm_num [c5,c6]; nlinarith
 have hresult := rank_one_minimum (weights i) u v (c5-c6) c5 hw
   (by norm_num [c5,c6]) (by norm_num [c5]) hd hu hv
 dsimp only at hresult
 have hmin : -(1/(4*(c5-c6)))*((∑ j, weights i j*v j^2)+
   c5/((c5-c6)-c5*(∑ j, weights i j*u j^2))*(∑ j, weights i j*u j*v j)^2) = evaluatedMinimum l i := by
  rw [hv2,hK,hU]
  have he : (c5-c6)-c5*(1/3+(l i)^2/2)=D l i := by unfold D; ring
  rw [he]; rfl
 rw [hmin] at hresult
 have hobjective (z : Fin 6 → ℝ) (hz : ∑ j, z j=0) :
   (c5-c6)*(∑ j, z j^2/weights i j)-c5*(∑ j, u j*z j)^2+∑ j, v j*z j = objective l i z := by
  have h1 : (∑ j, u j*z j) = ∑ j, l j*z j := by
   have he : (∑ j, u j*z j)=(∑ j, l j*z j)-(l i/4)*(∑ j, z j) := by
    simp only [u,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
   rw [he,hz]; ring
  have h2 : (∑ j, v j*z j) = ∑ j, V l i j*z j := by
   have he : (∑ j, v j*z j)=(∑ j, V l i j*z j)-m*(∑ j, z j) := by
    simp only [v,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]; ring
   rw [he,hz]; ring
  have h3 : (∑ j, z j^2/weights i j)=z i^2+3*(∑ j ∈ Finset.univ.erase i, z j^2) := by
   rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
   simp only [weights,ite_true,div_one]
   have he : (∑ j ∈ Finset.univ.erase i, z j^2/(if j=i then 1 else 1/3)) =
     3*(∑ j ∈ Finset.univ.erase i, z j^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro j hj
    have hn : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hn]; ring
   rw [he]
   ring
  rw [h1,h2,h3]; rfl
 constructor
 · intro z hz; rw [←hobjective z hz]; exact hresult.1 z
 · obtain ⟨z,hz,he⟩ := hresult.2
   exact ⟨z,hz,by rw [←hobjective z hz]; exact he⟩

theorem minimum_eq (l : Fin 6 → ℝ) (i : Fin 6)
 (htrace : ∑ j, l j=0) (hnorm : ∑ j, l j^2=1) :
 Paper.minimum l i = evaluatedMinimum l i := by
 have h := attains l i htrace hnorm
 apply IsLeast.csInf_eq
 change IsLeast {e : ℝ | ∃ z : Fin 6 → ℝ, (∑ j, z j)=0 ∧
   e=objective l i z} (evaluatedMinimum l i)
 constructor
 · obtain ⟨z,hz,he⟩ := h.2
   exact ⟨z,hz,he.symm⟩
 · rintro e ⟨z,hz,rfl⟩
   exact h.1 z hz

end R7.QuadraticMinimum
