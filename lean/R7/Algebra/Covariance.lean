import R7.Algebra.RankOne
import R7.Algebra.Projector
import R7.Spectral.Coordinates.Representation

noncomputable section
namespace R7.Core.Covariance
open scoped BigOperators Matrix
open Matrix
abbrev V := Fin 6 → ℝ

def weights (i : Fin 6) (j : Fin 6) : ℝ := if j=i then 1 else 1/3

def diagWeights (i : Fin 6) : Matrix (Fin 6) (Fin 6) ℝ :=
 diagonal (fun j => if j=i then 1 else 3)

def kernel (i : Fin 6) : Matrix (Fin 6) (Fin 6) ℝ :=
 diagonal (weights i) - (3/8:ℝ) • vecMulVec (weights i) (weights i)

def covariance (i : Fin 6) (u v : V) : ℝ :=
 (∑ j, weights i j*u j*v j) - (3/8)*(∑ j, weights i j*u j)*(∑ j, weights i j*v j)

def base (i : Fin 6) (R : BasisMatrix) : Matrix (Fin 5) (Fin 5) ℝ :=
 R.transpose * diagWeights i * R

def baseInverse (i : Fin 6) (R : BasisMatrix) : Matrix (Fin 5) (Fin 5) ℝ :=
 R.transpose * kernel i * R

@[simp] theorem weights_sum (i : Fin 6) : ∑ j, weights i j = 8/3 := by
 have h : weights i = fun j => (1/3:ℝ)+(if j=i then 2/3 else 0) := by
  funext j; by_cases h : j=i <;> simp [weights,h]; norm_num
 rw [h]
 simp [Finset.sum_add_distrib]
 norm_num

theorem kernel_symmetric (i : Fin 6) : (kernel i).transpose = kernel i := by
 simp [kernel,Matrix.transpose_vecMulVec]

theorem diag_mul_kernel (i : Fin 6) :
 diagWeights i * kernel i =
  1-(3/8:ℝ) • vecMulVec (fun _ => 1) (weights i) := by
 ext a b
 simp only [kernel,diagWeights,mul_sub,Matrix.diagonal_mul,
   Matrix.diagonal_apply,Matrix.vecMulVec_apply,Matrix.sub_apply,
   Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
 by_cases ha : a=i <;> by_cases hb : b=i <;> by_cases hab : a=b <;> simp_all [weights] <;> ring

theorem kernel_ones_left (i : Fin 6) :
 vecMulVec (fun _ : Fin 6 => (1:ℝ)) (fun _ : Fin 6 => (1:ℝ))*kernel i=0 := by
 ext a b
 simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, one_mul, kernel,
   Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
   Matrix.zero_apply, Finset.sum_sub_distrib]
 simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
 rw [show (∑ x : Fin 6, (3/8:ℝ)*(weights i x*weights i b)) =
       (3/8)*(∑ x : Fin 6, weights i x)*weights i b by
       simp only [Finset.mul_sum,Finset.sum_mul]; congr 1; funext x; ring]
 rw [weights_sum]
 ring

theorem kernel_ones_right (i : Fin 6) :
 kernel i*vecMulVec (fun _ : Fin 6 => (1:ℝ)) (fun _ : Fin 6 => (1:ℝ))=0 := by
 have h := congrArg Matrix.transpose (kernel_ones_left i)
 simpa only [Matrix.transpose_mul, Matrix.transpose_vecMulVec, kernel_symmetric,
   Matrix.transpose_zero] using h

theorem tracefree_transpose_ones (R : BasisMatrix) (hz : ∀ a, ∑ j, R j a=0)
    (w : V) : R.transpose * vecMulVec (fun _ : Fin 6 => (1:ℝ)) w = 0 := by
 ext a b
 simp [Matrix.mul_apply, Matrix.vecMulVec_apply,Matrix.transpose_apply,
   ← Finset.sum_mul,hz]

theorem base_mul_inverse (i : Fin 6) (R : BasisMatrix)
 (horth : R.transpose*R=1) (hz : ∀ a, ∑ j, R j a=0)
 (hproj : R*R.transpose = 1-(1/6:ℝ) • vecMulVec (fun _=>1) (fun _=>1)) :
 base i R*baseInverse i R=1 := by
 have hp : (R*R.transpose)*kernel i=kernel i := by
  rw [hproj,sub_mul,Matrix.one_mul,Matrix.smul_mul,kernel_ones_left,smul_zero,sub_zero]
 unfold base baseInverse
 calc
  _ = R.transpose*diagWeights i*((R*R.transpose)*kernel i)*R := by
    simp only [Matrix.mul_assoc]
  _ = R.transpose*(diagWeights i*kernel i)*R := by rw [hp]; simp only [Matrix.mul_assoc]
  _ = R.transpose*(1-(3/8:ℝ) • vecMulVec (fun _=>1) (weights i))*R := by rw [diag_mul_kernel]
  _ = 1 := by rw [Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,
    tracefree_transpose_ones R hz,smul_zero,sub_zero,horth]

theorem baseInverse_symmetric (i : Fin 6) (R : BasisMatrix) :
 (baseInverse i R).transpose=baseInverse i R := by
 simp only [baseInverse,Matrix.transpose_mul,Matrix.transpose_transpose,kernel_symmetric]
 simp only [Matrix.mul_assoc]

theorem covariance_eq_dot (i : Fin 6) (u v : V) :
 covariance i u v = u ⬝ᵥ (kernel i*ᵥv) := by
 have hdiag : u ⬝ᵥ (diagonal (weights i)*ᵥv) = ∑ j, weights i j*u j*v j := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl; intro j hj; ring
 have hout : u ⬝ᵥ (vecMulVec (weights i) (weights i)*ᵥv) =
   (∑ j, weights i j*u j)*(∑ j, weights i j*v j) := by
  rw [Matrix.vecMulVec_mulVec]
  rw [op_smul_eq_smul, dotProduct_smul]
  simp only [dotProduct,smul_eq_mul]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl; intro j hj; ring
 rw [kernel,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,dotProduct_smul,
   hdiag,hout]
 simp only [covariance,smul_eq_mul,mul_assoc]

theorem projected_kernel_pair (i : Fin 6) (R : BasisMatrix)
 (horth : R.transpose*R=1) (hz : ∀ a, ∑ j, R j a=0) (u v : V) :
 (projected R u) ⬝ᵥ (baseInverse i R*ᵥprojected R v) = covariance i u v := by
 have hp : R*R.transpose = 1-(1/6:ℝ) • vecMulVec (fun _=>1) (fun _=>1) := by
  simpa [Matrix.vecMulVec] using R7.Core.six_five_projector R horth hz
 have hPK : (R*R.transpose)*kernel i=kernel i := by
  rw [hp,sub_mul,Matrix.one_mul,Matrix.smul_mul,kernel_ones_left,smul_zero,sub_zero]
 have hKP : kernel i*(R*R.transpose)=kernel i := by
  rw [hp,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,kernel_ones_right,smul_zero,sub_zero]
 have hx (u : V) : projected R u = R.transpose*ᵥu := rfl
 rw [hx,hx,baseInverse]
 rw [Matrix.mulVec_transpose,←Matrix.dotProduct_mulVec]
 simp only [Matrix.mulVec_mulVec]
 have hmat : R*(R.transpose*kernel i*R)*R.transpose=kernel i := by
  calc
   _ = ((R*R.transpose)*kernel i)*(R*R.transpose) := by simp only [Matrix.mul_assoc]
   _ = kernel i := by rw [hPK,hKP]
 have hmat' : R*(R.transpose*kernel i*R*R.transpose)=kernel i := by
  simpa only [Matrix.mul_assoc] using hmat
 rw [hmat']
 exact (covariance_eq_dot i u v).symm

theorem weighted_sum (i : Fin 6) (f : V) :
 (∑ j, weights i j*f j) = (1/3)*(∑ j, f j)+(2/3)*f i := by
 have h : weights i = fun j => (1/3:ℝ)+(if j=i then 2/3 else 0) := by
  funext j; by_cases h : j=i <;> simp [weights,h]; norm_num
 simp only [h,add_mul,Finset.sum_add_distrib]
 rw [←Finset.mul_sum]
 simp

theorem normalized_coordinate_bound (l : Spectrum) (hl : Normalized l) (i : Fin 6) :
 (l i)^2 ≤ 5/6 := by
 have hs : (l i+l i/5)^2 ≤ ∑ j : Fin 6, (l j+l i/5)^2 :=
  Finset.single_le_sum (fun j _ => sq_nonneg (l j+l i/5)) (Finset.mem_univ i)
 have heq : (∑ j : Fin 6, (l j+l i/5)^2) = 1+6*(l i/5)^2 := by
  simp only [add_sq,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  rw [hl.1,hl.2]
  simp
 rw [heq] at hs
 nlinarith

theorem covariance_self_normalized (l : Spectrum) (hl : Normalized l) (i : Fin 6) :
 covariance i l l = 1/3+(l i)^2/2 := by
 unfold covariance
 have hs : (∑ j, weights i j*l j*l j) = (1/3)*(∑ j, (l j)^2)+(2/3)*(l i)^2 := by
  simpa only [pow_two,mul_assoc] using weighted_sum i (fun j => l j*l j)
 rw [hs,weighted_sum i l,hl.1,hl.2]
 ring

theorem cMatrix_terminal (l : Spectrum) (i : Fin 6) (R : BasisMatrix) :
 cMatrix (terminalParameters) l i R = (138/25:ℝ) • base i R
   -(151/25:ℝ) • vecMulVec (projected R l) (projected R l) := by
 have hd : ((terminalParameters).m22:ℝ)=151/25 := by
  have h : (terminalParameters).m22=151/25 := rfl
  rw [h]; norm_num
 have hc : ((terminalParameters).c6:ℝ)=13/25 := by
  have h : (terminalParameters).c6=13/25 := rfl
  rw [h]; norm_num
 have he : ((terminalParameters).c13:ℝ)=0 := by
  have h : (terminalParameters).c13=0 := by decide
  rw [h]; norm_num
 have hraw : (fun j k : Fin 6 =>
    (if j=k then ((151:ℝ)/25-13/25)*(if j=i then 1 else 3) else 0)
      -(151/25)*l j*l k) =
      (138/25:ℝ) • diagWeights i -(151/25:ℝ) • vecMulVec l l := by
  ext j k
  by_cases h : j=k <;> by_cases hj : j=i <;> simp_all [diagWeights,Matrix.vecMulVec_apply,smul_eq_mul] <;> ring
 unfold cMatrix
 simp only [hd,hc,he,zero_mul,sub_zero]
 rw [hraw]
 simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
   base, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
 have hl : R.transpose*ᵥl=projected R l := rfl
 have hr : l ᵥ*R=projected R l := by
  rw [←Matrix.mulVec_transpose]; exact hl
 rw [hl,hr]

theorem inversePair_eq_dot (C : Matrix (Fin 5) (Fin 5) ℝ) (u v : Fin 5 → ℝ) :
 inversePair C u v = u ⬝ᵥ (C⁻¹*ᵥv) := by
 simp only [inversePair,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

theorem inversePair_covariance (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
 (hl : Normalized l) (hR : IsTraceFreeOrthonormalBasis R) (v : V) :
 inversePair (cMatrix (terminalParameters) l i R) (projected R v) (projected R v) =
  covariance i v v/(138/25)
   +(151/25)*(covariance i v l)^2 /
      ((138/25)*((138/25)-(151/25)*(1/3+(l i)^2/2))) := by
 have hp : R*R.transpose = 1-(1/6:ℝ) • vecMulVec (fun _=>1) (fun _=>1) := by
  simpa [Matrix.vecMulVec] using R7.Core.six_five_projector R hR.1 hR.2
 have hδ : (138/25:ℝ)-(151/25)*((projected R l) ⬝ᵥ (baseInverse i R*ᵥprojected R l)) ≠ 0 := by
  rw [projected_kernel_pair i R hR.1 hR.2,covariance_self_normalized l hl i]
  have hb := normalized_coordinate_bound l hl i
  have : (0:ℝ) < 138/25-(151/25)*(1/3+(l i)^2/2) := by nlinarith
  exact ne_of_gt this
 have h := RankOne.pairing_update (base i R) (baseInverse i R)
   (projected R l) (projected R v) (138/25) (151/25)
   (base_mul_inverse i R hR.1 hR.2 hp) (baseInverse_symmetric i R)
   (by norm_num) hδ
 rw [←cMatrix_terminal l i R] at h
 rw [inversePair_eq_dot]
 rw [projected_kernel_pair i R hR.1 hR.2,
   projected_kernel_pair i R hR.1 hR.2,
   projected_kernel_pair i R hR.1 hR.2,
   covariance_self_normalized l hl i] at h
 exact h

theorem tracefree_coordinate_bound (l : Spectrum) (ht : (∑ j, l j)=0) (i : Fin 6) :
 (l i)^2 ≤ (5/6)*(∑ j, (l j)^2) := by
 have hs : (l i+l i/5)^2 ≤ ∑ j : Fin 6, (l j+l i/5)^2 :=
  Finset.single_le_sum (fun j _ => sq_nonneg (l j+l i/5)) (Finset.mem_univ i)
 have heq : (∑ j : Fin 6, (l j+l i/5)^2) =
   (∑ j, (l j)^2)+6*(l i/5)^2 := by
  simp only [add_sq,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  rw [ht]
  simp
 rw [heq] at hs
 nlinarith

end R7.Core.Covariance
