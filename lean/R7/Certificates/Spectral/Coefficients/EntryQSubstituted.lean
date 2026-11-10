import R7.Spectral.Kronecker.ReducedGapCertificate
import R7.Spectral.Kronecker.Core
import R7.Certificates.Spectral.Coefficients.EntryQGroups
import R7.Certificates.Spectral.Coefficients.GapPowers
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryQg0 : subHom (interpretKey entryQG0) = interpretKey entryQO0 := by
  have hz : ∀ a∈entryQG0, a.exp 0=0 := by
    have hh : entryQG0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPowerData0_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryQG0 gapPowerData0 entryQO0 12 0
    (by decide) (by decide +kernel) gapPowerData0_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryQg1 : subHom (interpretKey entryQG1) = interpretKey entryQO1 := by
  have hz : ∀ a∈entryQG1, a.exp 0=1 := by
    have hh : entryQG1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPowerData1_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryQG1 gapPowerData1 entryQO1 12 1
    (by decide) (by decide +kernel) gapPowerData1_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryQg2 : subHom (interpretKey entryQG2) = interpretKey entryQO2 := by
  have hz : ∀ a∈entryQG2, a.exp 0=2 := by
    have hh : entryQG2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  exact Kronecker.Reduced.multiply_gap 13 2 12 entryQG2 entryQO2
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 81)
    (by decide +kernel) (by decide +kernel)

theorem entryQg3 : subHom (interpretKey entryQG3) = interpretKey entryQO3 := by
  have hz : ∀ a∈entryQG3, a.exp 0=3 := by
    have hh : entryQG3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  exact Kronecker.Reduced.multiply_gap 13 3 12 entryQG3 entryQO3
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 79)
    (by decide +kernel) (by decide +kernel)

theorem entryQg4 : subHom (interpretKey entryQG4) = interpretKey entryQO4 := by
  have hz : ∀ a∈entryQG4, a.exp 0=4 := by
    have hh : entryQG4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  exact Kronecker.Reduced.multiply_gap 13 4 12 entryQG4 entryQO4
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 83)
    (by decide +kernel) (by decide +kernel)

theorem entryQg5 : subHom (interpretKey entryQG5) = interpretKey entryQO5 := by
  have hz : ∀ a∈entryQG5, a.exp 0=5 := by
    have hh : entryQG5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  exact Kronecker.Reduced.multiply_gap 13 5 12 entryQG5 entryQO5
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 80)
    (by decide +kernel) (by decide +kernel)

theorem entryQg6 : subHom (interpretKey entryQG6) = interpretKey entryQO6 := by
  have hz : ∀ a∈entryQG6, a.exp 0=6 := by
    have hh : entryQG6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  exact Kronecker.Reduced.multiply_gap 13 6 12 entryQG6 entryQO6
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 84)
    (by decide +kernel) (by decide +kernel)

theorem entryQg7 : subHom (interpretKey entryQG7) = interpretKey entryQO7 := by
  have hz : ∀ a∈entryQG7, a.exp 0=7 := by
    have hh : entryQG7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  exact Kronecker.Reduced.multiply_gap 13 7 12 entryQG7 entryQO7
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 80)
    (by decide +kernel) (by decide +kernel)

theorem entryQg8 : subHom (interpretKey entryQG8) = interpretKey entryQO8 := by
  have hz : ∀ a∈entryQG8, a.exp 0=8 := by
    have hh : entryQG8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  exact Kronecker.Reduced.multiply_gap 13 8 12 entryQG8 entryQO8
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 84)
    (by decide +kernel) (by decide +kernel)

theorem entryQg9 : subHom (interpretKey entryQG9) = interpretKey entryQO9 := by
  have hz : ∀ a∈entryQG9, a.exp 0=9 := by
    have hh : entryQG9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  exact Kronecker.Reduced.multiply_gap 13 9 12 entryQG9 entryQO9
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 79)
    (by decide +kernel) (by decide +kernel)

theorem entryQg10 : subHom (interpretKey entryQG10) = interpretKey entryQO10 := by
  have hz : ∀ a∈entryQG10, a.exp 0=10 := by
    have hh : entryQG10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  exact Kronecker.Reduced.multiply_gap 13 10 12 entryQG10 entryQO10
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (B := R7.Algebra.KernelPower.fastPow 2 82)
    (by decide +kernel) (by decide +kernel)

theorem entryQg11 : subHom (interpretKey entryQG11) = interpretKey entryQO11 := by
  have hz : ∀ a∈entryQG11, a.exp 0=11 := by
    have hh : entryQG11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPowerData11_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryQG11 gapPowerData11 entryQO11 12 11
    (by decide) (by decide +kernel) gapPowerData11_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryQg12 : subHom (interpretKey entryQG12) = interpretKey entryQO12 := by
  have hz : ∀ a∈entryQG12, a.exp 0=12 := by
    have hh : entryQG12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPowerData12_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply entryQG12 gapPowerData12 entryQO12 12 12
    (by decide) (by decide +kernel) gapPowerData12_integer_view
    (by decide +kernel) (by decide +kernel)
theorem entryQ_substitution : interpretKey entryQData=subHom (interpretKey p308) := by
  have hr :
      addKey
        (addKey (addKey entryQG0 (addKey entryQG1 entryQG2))
          (addKey entryQG3 (addKey entryQG4 entryQG5)))
        (addKey (addKey entryQG6 (addKey entryQG7 entryQG8))
          (addKey (addKey entryQG9 entryQG10) (addKey entryQG11 entryQG12))) = p308 :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  have ho :
      addKey
        (addKey (addKey entryQO0 (addKey entryQO1 entryQO2))
          (addKey entryQO3 (addKey entryQO4 entryQO5)))
        (addKey (addKey entryQO6 (addKey entryQO7 entryQO8))
          (addKey (addKey entryQO9 entryQO10) (addKey entryQO11 entryQO12))) = entryQData :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,← hr]
  simp only [interpretKey_add,map_add,entryQg0,entryQg1,entryQg2,entryQg3,entryQg4,entryQg5,entryQg6,entryQg7,entryQg8,entryQg9,entryQg10,entryQg11,entryQg12]
end R7.Core.SpectralCoefficient.Expansion
