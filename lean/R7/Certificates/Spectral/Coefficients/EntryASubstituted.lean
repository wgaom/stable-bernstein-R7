import R7.Spectral.Kronecker.ReducedGapCertificate
import R7.Spectral.Kronecker.Core
import R7.Certificates.Spectral.Coefficients.EntryAGroups
import R7.Certificates.Spectral.Coefficients.GapPowers
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryAg0 : subHom (interpretKey entryAG0) = interpretKey entryAO0 := by
  have hz : ∀ a∈entryAG0, a.exp 0=0 := by
    have hh : entryAG0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPowerData0_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG0 gapPowerData0 entryAO0 12 0
    (by decide) (by decide +kernel) gapPowerData0_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg1 : subHom (interpretKey entryAG1) = interpretKey entryAO1 := by
  have hz : ∀ a∈entryAG1, a.exp 0=1 := by
    have hh : entryAG1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPowerData1_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG1 gapPowerData1 entryAO1 12 1
    (by decide) (by decide +kernel) gapPowerData1_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg2 : subHom (interpretKey entryAG2) = interpretKey entryAO2 := by
  have hz : ∀ a∈entryAG2, a.exp 0=2 := by
    have hh : entryAG2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  exact Kronecker.Reduced.multiply_gap 13 2 12 entryAG2 entryAO2
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 73)
    (by decide +kernel) (by decide +kernel)

theorem entryAg3 : subHom (interpretKey entryAG3) = interpretKey entryAO3 := by
  have hz : ∀ a∈entryAG3, a.exp 0=3 := by
    have hh : entryAG3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  rw [← gapPowerData3_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG3 gapPowerData3 entryAO3 12 3
    (by decide) (by decide +kernel) gapPowerData3_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg4 : subHom (interpretKey entryAG4) = interpretKey entryAO4 := by
  have hz : ∀ a∈entryAG4, a.exp 0=4 := by
    have hh : entryAG4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  exact Kronecker.Reduced.multiply_gap 13 4 12 entryAG4 entryAO4
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 75)
    (by decide +kernel) (by decide +kernel)

theorem entryAg5 : subHom (interpretKey entryAG5) = interpretKey entryAO5 := by
  have hz : ∀ a∈entryAG5, a.exp 0=5 := by
    have hh : entryAG5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  rw [← gapPowerData5_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG5 gapPowerData5 entryAO5 12 5
    (by decide) (by decide +kernel) gapPowerData5_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg6 : subHom (interpretKey entryAG6) = interpretKey entryAO6 := by
  have hz : ∀ a∈entryAG6, a.exp 0=6 := by
    have hh : entryAG6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  exact Kronecker.Reduced.multiply_gap 13 6 12 entryAG6 entryAO6
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 76)
    (by decide +kernel) (by decide +kernel)

theorem entryAg7 : subHom (interpretKey entryAG7) = interpretKey entryAO7 := by
  have hz : ∀ a∈entryAG7, a.exp 0=7 := by
    have hh : entryAG7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  rw [← gapPowerData7_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG7 gapPowerData7 entryAO7 12 7
    (by decide) (by decide +kernel) gapPowerData7_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg8 : subHom (interpretKey entryAG8) = interpretKey entryAO8 := by
  have hz : ∀ a∈entryAG8, a.exp 0=8 := by
    have hh : entryAG8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  exact Kronecker.Reduced.multiply_gap 13 8 12 entryAG8 entryAO8
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 77)
    (by decide +kernel) (by decide +kernel)

theorem entryAg9 : subHom (interpretKey entryAG9) = interpretKey entryAO9 := by
  have hz : ∀ a∈entryAG9, a.exp 0=9 := by
    have hh : entryAG9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  rw [← gapPowerData9_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG9 gapPowerData9 entryAO9 12 9
    (by decide) (by decide +kernel) gapPowerData9_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg10 : subHom (interpretKey entryAG10) = interpretKey entryAO10 := by
  have hz : ∀ a∈entryAG10, a.exp 0=10 := by
    have hh : entryAG10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  exact Kronecker.Reduced.multiply_gap 13 10 12 entryAG10 entryAO10
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 76)
    (by decide +kernel) (by decide +kernel)

theorem entryAg11 : subHom (interpretKey entryAG11) = interpretKey entryAO11 := by
  have hz : ∀ a∈entryAG11, a.exp 0=11 := by
    have hh : entryAG11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPowerData11_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG11 gapPowerData11 entryAO11 12 11
    (by decide) (by decide +kernel) gapPowerData11_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryAg12 : subHom (interpretKey entryAG12) = interpretKey entryAO12 := by
  have hz : ∀ a∈entryAG12, a.exp 0=12 := by
    have hh : entryAG12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPowerData12_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryAG12 gapPowerData12 entryAO12 12 12
    (by decide) (by decide +kernel) gapPowerData12_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryA_substitution : interpretKey entryAData=subHom (interpretKey p59) := by
  have hr :
      addKey
        (addKey (addKey entryAG0 (addKey entryAG1 entryAG2))
          (addKey entryAG3 (addKey entryAG4 entryAG5)))
        (addKey (addKey entryAG6 (addKey entryAG7 entryAG8))
          (addKey (addKey entryAG9 entryAG10) (addKey entryAG11 entryAG12))) = p59 :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  have ho :
      addKey
        (addKey (addKey entryAO0 (addKey entryAO1 entryAO2))
          (addKey entryAO3 (addKey entryAO4 entryAO5)))
        (addKey (addKey entryAO6 (addKey entryAO7 entryAO8))
          (addKey (addKey entryAO9 entryAO10) (addKey entryAO11 entryAO12))) = entryAData :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,← hr]
  simp only [interpretKey_add,map_add,entryAg0,entryAg1,entryAg2,entryAg3,entryAg4,entryAg5,entryAg6,entryAg7,entryAg8,entryAg9,entryAg10,entryAg11,entryAg12]
end R7.Core.SpectralCoefficient.Expansion
