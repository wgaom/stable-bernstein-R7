import R7.Spectral.Kronecker.ReducedGapCertificate
import R7.Spectral.Kronecker.Core
import R7.Certificates.Spectral.Coefficients.CriticalQ8Groups
import R7.Certificates.Spectral.Coefficients.GapPowers
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem criticalQ8g0 : subHom (interpretKey criticalQ8G0) = interpretKey criticalQ8O0 := by
  have hz : ∀ a∈criticalQ8G0, a.exp 0=0 := by
    have hh : criticalQ8G0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPowerData0_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G0 gapPowerData0 criticalQ8O0 8 0
    (by decide) (by decide +kernel) gapPowerData0_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g1 : subHom (interpretKey criticalQ8G1) = interpretKey criticalQ8O1 := by
  have hz : ∀ a∈criticalQ8G1, a.exp 0=1 := by
    have hh : criticalQ8G1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPowerData1_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G1 gapPowerData1 criticalQ8O1 8 1
    (by decide) (by decide +kernel) gapPowerData1_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g2 : subHom (interpretKey criticalQ8G2) = interpretKey criticalQ8O2 := by
  have hz : ∀ a∈criticalQ8G2, a.exp 0=2 := by
    have hh : criticalQ8G2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  rw [← gapPowerData2_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G2 gapPowerData2 criticalQ8O2 8 2
    (by decide) (by decide +kernel) gapPowerData2_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g3 : subHom (interpretKey criticalQ8G3) = interpretKey criticalQ8O3 := by
  have hz : ∀ a∈criticalQ8G3, a.exp 0=3 := by
    have hh : criticalQ8G3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  rw [← gapPowerData3_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G3 gapPowerData3 criticalQ8O3 8 3
    (by decide) (by decide +kernel) gapPowerData3_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g4 : subHom (interpretKey criticalQ8G4) = interpretKey criticalQ8O4 := by
  have hz : ∀ a∈criticalQ8G4, a.exp 0=4 := by
    have hh : criticalQ8G4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  rw [← gapPowerData4_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G4 gapPowerData4 criticalQ8O4 8 4
    (by decide) (by decide +kernel) gapPowerData4_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g5 : subHom (interpretKey criticalQ8G5) = interpretKey criticalQ8O5 := by
  have hz : ∀ a∈criticalQ8G5, a.exp 0=5 := by
    have hh : criticalQ8G5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  rw [← gapPowerData5_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G5 gapPowerData5 criticalQ8O5 8 5
    (by decide) (by decide +kernel) gapPowerData5_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g6 : subHom (interpretKey criticalQ8G6) = interpretKey criticalQ8O6 := by
  have hz : ∀ a∈criticalQ8G6, a.exp 0=6 := by
    have hh : criticalQ8G6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  rw [← gapPowerData6_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G6 gapPowerData6 criticalQ8O6 8 6
    (by decide) (by decide +kernel) gapPowerData6_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g7 : subHom (interpretKey criticalQ8G7) = interpretKey criticalQ8O7 := by
  have hz : ∀ a∈criticalQ8G7, a.exp 0=7 := by
    have hh : criticalQ8G7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  rw [← gapPowerData7_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G7 gapPowerData7 criticalQ8O7 8 7
    (by decide) (by decide +kernel) gapPowerData7_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g8 : subHom (interpretKey criticalQ8G8) = interpretKey criticalQ8O8 := by
  have hz : ∀ a∈criticalQ8G8, a.exp 0=8 := by
    have hh : criticalQ8G8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  rw [← gapPowerData8_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G8 gapPowerData8 criticalQ8O8 8 8
    (by decide) (by decide +kernel) gapPowerData8_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g9 : subHom (interpretKey criticalQ8G9) = interpretKey criticalQ8O9 := by
  have hz : ∀ a∈criticalQ8G9, a.exp 0=9 := by
    have hh : criticalQ8G9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  rw [← gapPowerData9_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G9 gapPowerData9 criticalQ8O9 8 9
    (by decide) (by decide +kernel) gapPowerData9_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g10 : subHom (interpretKey criticalQ8G10) = interpretKey criticalQ8O10 := by
  have hz : ∀ a∈criticalQ8G10, a.exp 0=10 := by
    have hh : criticalQ8G10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  rw [← gapPowerData10_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G10 gapPowerData10 criticalQ8O10 8 10
    (by decide) (by decide +kernel) gapPowerData10_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g11 : subHom (interpretKey criticalQ8G11) = interpretKey criticalQ8O11 := by
  have hz : ∀ a∈criticalQ8G11, a.exp 0=11 := by
    have hh : criticalQ8G11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPowerData11_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G11 gapPowerData11 criticalQ8O11 8 11
    (by decide) (by decide +kernel) gapPowerData11_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8g12 : subHom (interpretKey criticalQ8G12) = interpretKey criticalQ8O12 := by
  have hz : ∀ a∈criticalQ8G12, a.exp 0=12 := by
    have hh : criticalQ8G12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPowerData12_correct]
  exact R7.Core.SpectralCoefficient.Kronecker.IntegerView.multiply criticalQ8G12 gapPowerData12 criticalQ8O12 8 12
    (by decide) (by decide +kernel) gapPowerData12_integer_view
    (by decide +kernel) (by decide +kernel)
theorem criticalQ8_substitution : interpretKey criticalQ8Data=subHom (interpretKey p332) := by
  have hr :
      addKey
        (addKey (addKey criticalQ8G0 (addKey criticalQ8G1 criticalQ8G2))
          (addKey criticalQ8G3 (addKey criticalQ8G4 criticalQ8G5)))
        (addKey (addKey criticalQ8G6 (addKey criticalQ8G7 criticalQ8G8))
          (addKey (addKey criticalQ8G9 criticalQ8G10) (addKey criticalQ8G11 criticalQ8G12))) = p332 :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  have ho :
      addKey
        (addKey (addKey criticalQ8O0 (addKey criticalQ8O1 criticalQ8O2))
          (addKey criticalQ8O3 (addKey criticalQ8O4 criticalQ8O5)))
        (addKey (addKey criticalQ8O6 (addKey criticalQ8O7 criticalQ8O8))
          (addKey (addKey criticalQ8O9 criticalQ8O10) (addKey criticalQ8O11 criticalQ8O12))) = criticalQ8Data :=
    keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,← hr]
  simp only [interpretKey_add,map_add,criticalQ8g0,criticalQ8g1,criticalQ8g2,criticalQ8g3,criticalQ8g4,criticalQ8g5,criticalQ8g6,criticalQ8g7,criticalQ8g8,criticalQ8g9,criticalQ8g10,criticalQ8g11,criticalQ8g12]
end R7.Core.SpectralCoefficient.Expansion
