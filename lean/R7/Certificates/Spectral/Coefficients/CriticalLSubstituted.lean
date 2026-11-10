import R7.Spectral.Kronecker.ReducedGapCertificate
import R7.Spectral.Kronecker.Core
import R7.Certificates.Spectral.Coefficients.CriticalLGroups
import R7.Certificates.Spectral.Coefficients.GapPowers
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem criticalLg0 : subHom (interpretKey criticalLG0) = interpretKey criticalLO0 := by
  have hz : ∀ a∈criticalLG0, a.exp 0=0 := by
    have hh : criticalLG0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPowerData0_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalLG0 gapPowerData0 criticalLO0 12 0
    (by decide) (by decide +kernel) gapPowerData0_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalLg1 : subHom (interpretKey criticalLG1) = interpretKey criticalLO1 := by
  have hz : ∀ a∈criticalLG1, a.exp 0=1 := by
    have hh : criticalLG1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPowerData1_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalLG1 gapPowerData1 criticalLO1 12 1
    (by decide) (by decide +kernel) gapPowerData1_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalLg2 : subHom (interpretKey criticalLG2) = interpretKey criticalLO2 := by
  have hz : ∀ a∈criticalLG2, a.exp 0=2 := by
    have hh : criticalLG2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  exact Kronecker.Reduced.multiply_gap 13 2 12 criticalLG2 criticalLO2
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 78)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg3 : subHom (interpretKey criticalLG3) = interpretKey criticalLO3 := by
  have hz : ∀ a∈criticalLG3, a.exp 0=3 := by
    have hh : criticalLG3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  exact Kronecker.Reduced.multiply_gap 13 3 12 criticalLG3 criticalLO3
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 75)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg4 : subHom (interpretKey criticalLG4) = interpretKey criticalLO4 := by
  have hz : ∀ a∈criticalLG4, a.exp 0=4 := by
    have hh : criticalLG4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  exact Kronecker.Reduced.multiply_gap 13 4 12 criticalLG4 criticalLO4
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 80)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg5 : subHom (interpretKey criticalLG5) = interpretKey criticalLO5 := by
  have hz : ∀ a∈criticalLG5, a.exp 0=5 := by
    have hh : criticalLG5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  exact Kronecker.Reduced.multiply_gap 13 5 12 criticalLG5 criticalLO5
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 76)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg6 : subHom (interpretKey criticalLG6) = interpretKey criticalLO6 := by
  have hz : ∀ a∈criticalLG6, a.exp 0=6 := by
    have hh : criticalLG6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  exact Kronecker.Reduced.multiply_gap 13 6 12 criticalLG6 criticalLO6
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 81)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg7 : subHom (interpretKey criticalLG7) = interpretKey criticalLO7 := by
  have hz : ∀ a∈criticalLG7, a.exp 0=7 := by
    have hh : criticalLG7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  exact Kronecker.Reduced.multiply_gap 13 7 12 criticalLG7 criticalLO7
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 73)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg8 : subHom (interpretKey criticalLG8) = interpretKey criticalLO8 := by
  have hz : ∀ a∈criticalLG8, a.exp 0=8 := by
    have hh : criticalLG8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  exact Kronecker.Reduced.multiply_gap 13 8 12 criticalLG8 criticalLO8
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 81)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg9 : subHom (interpretKey criticalLG9) = interpretKey criticalLO9 := by
  have hz : ∀ a∈criticalLG9, a.exp 0=9 := by
    have hh : criticalLG9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  exact Kronecker.Reduced.multiply_gap 13 9 12 criticalLG9 criticalLO9
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 74)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg10 : subHom (interpretKey criticalLG10) = interpretKey criticalLO10 := by
  have hz : ∀ a∈criticalLG10, a.exp 0=10 := by
    have hh : criticalLG10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  exact Kronecker.Reduced.multiply_gap 13 10 12 criticalLG10 criticalLO10
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 80)
    (by decide +kernel) (by decide +kernel)

theorem criticalLg11 : subHom (interpretKey criticalLG11) = interpretKey criticalLO11 := by
  have hz : ∀ a∈criticalLG11, a.exp 0=11 := by
    have hh : criticalLG11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPowerData11_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalLG11 gapPowerData11 criticalLO11 12 11
    (by decide) (by decide +kernel) gapPowerData11_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalLg12 : subHom (interpretKey criticalLG12) = interpretKey criticalLO12 := by
  have hz : ∀ a∈criticalLG12, a.exp 0=12 := by
    have hh : criticalLG12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPowerData12_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalLG12 gapPowerData12 criticalLO12 12 12
    (by decide) (by decide +kernel) gapPowerData12_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalL_substitution : interpretKey criticalLData=subHom (interpretKey p330) := by
  have hr :
      addKey
        (addKey (addKey criticalLG0 (addKey criticalLG1 criticalLG2))
          (addKey criticalLG3 (addKey criticalLG4 criticalLG5)))
        (addKey (addKey criticalLG6 (addKey criticalLG7 criticalLG8))
          (addKey (addKey criticalLG9 criticalLG10) (addKey criticalLG11 criticalLG12))) = p330 :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  have ho :
      addKey
        (addKey (addKey criticalLO0 (addKey criticalLO1 criticalLO2))
          (addKey criticalLO3 (addKey criticalLO4 criticalLO5)))
        (addKey (addKey criticalLO6 (addKey criticalLO7 criticalLO8))
          (addKey (addKey criticalLO9 criticalLO10) (addKey criticalLO11 criticalLO12))) = criticalLData :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,← hr]
  simp only [interpretKey_add,map_add,criticalLg0,criticalLg1,criticalLg2,criticalLg3,criticalLg4,criticalLg5,criticalLg6,criticalLg7,criticalLg8,criticalLg9,criticalLg10,criticalLg11,criticalLg12]
end R7.Core.SpectralCoefficient.Expansion
