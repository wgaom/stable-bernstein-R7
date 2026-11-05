import R7.Certificates.Spectral.Coefficients.CriticalLGroups
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem criticalLg0 : subHom (interpretKey criticalLG0) = interpretKey criticalLO0 := by
  have hz : ∀ a∈criticalLG0, a.exp 0=0 := by
    have hh : criticalLG0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPower_correct 0,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg1 : subHom (interpretKey criticalLG1) = interpretKey criticalLO1 := by
  have hz : ∀ a∈criticalLG1, a.exp 0=1 := by
    have hh : criticalLG1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPower_correct 1,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg2 : subHom (interpretKey criticalLG2) = interpretKey criticalLO2 := by
  have hz : ∀ a∈criticalLG2, a.exp 0=2 := by
    have hh : criticalLG2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  rw [← gapPower_correct 2,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg3 : subHom (interpretKey criticalLG3) = interpretKey criticalLO3 := by
  have hz : ∀ a∈criticalLG3, a.exp 0=3 := by
    have hh : criticalLG3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  rw [← gapPower_correct 3,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg4 : subHom (interpretKey criticalLG4) = interpretKey criticalLO4 := by
  have hz : ∀ a∈criticalLG4, a.exp 0=4 := by
    have hh : criticalLG4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  rw [← gapPower_correct 4,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg5 : subHom (interpretKey criticalLG5) = interpretKey criticalLO5 := by
  have hz : ∀ a∈criticalLG5, a.exp 0=5 := by
    have hh : criticalLG5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  rw [← gapPower_correct 5,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg6 : subHom (interpretKey criticalLG6) = interpretKey criticalLO6 := by
  have hz : ∀ a∈criticalLG6, a.exp 0=6 := by
    have hh : criticalLG6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  rw [← gapPower_correct 6,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg7 : subHom (interpretKey criticalLG7) = interpretKey criticalLO7 := by
  have hz : ∀ a∈criticalLG7, a.exp 0=7 := by
    have hh : criticalLG7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  rw [← gapPower_correct 7,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg8 : subHom (interpretKey criticalLG8) = interpretKey criticalLO8 := by
  have hz : ∀ a∈criticalLG8, a.exp 0=8 := by
    have hh : criticalLG8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  rw [← gapPower_correct 8,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg9 : subHom (interpretKey criticalLG9) = interpretKey criticalLO9 := by
  have hz : ∀ a∈criticalLG9, a.exp 0=9 := by
    have hh : criticalLG9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  rw [← gapPower_correct 9,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg10 : subHom (interpretKey criticalLG10) = interpretKey criticalLO10 := by
  have hz : ∀ a∈criticalLG10, a.exp 0=10 := by
    have hh : criticalLG10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  rw [← gapPower_correct 10,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg11 : subHom (interpretKey criticalLG11) = interpretKey criticalLO11 := by
  have hz : ∀ a∈criticalLG11, a.exp 0=11 := by
    have hh : criticalLG11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPower_correct 11,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalLg12 : subHom (interpretKey criticalLG12) = interpretKey criticalLO12 := by
  have hz : ∀ a∈criticalLG12, a.exp 0=12 := by
    have hh : criticalLG12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPower_correct 12,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem criticalL_substitution : interpretKey criticalLData=subHom (interpretKey p330) := by
  have hr : normalizeKey (criticalLG0 ++ criticalLG1 ++ criticalLG2 ++ criticalLG3 ++ criticalLG4 ++ criticalLG5 ++ criticalLG6 ++ criticalLG7 ++ criticalLG8 ++ criticalLG9 ++ criticalLG10 ++ criticalLG11 ++ criticalLG12)=p330 := keyPolyEqual_sound _ _ (by decide +kernel)
  have ho : normalizeKey (criticalLO0 ++ criticalLO1 ++ criticalLO2 ++ criticalLO3 ++ criticalLO4 ++ criticalLO5 ++ criticalLO6 ++ criticalLO7 ++ criticalLO8 ++ criticalLO9 ++ criticalLO10 ++ criticalLO11 ++ criticalLO12)=criticalLData := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,interpret_normalizeKey,← hr,interpret_normalizeKey]
  simp only [interpretKey_append,map_add,criticalLg0,criticalLg1,criticalLg2,criticalLg3,criticalLg4,criticalLg5,criticalLg6,criticalLg7,criticalLg8,criticalLg9,criticalLg10,criticalLg11,criticalLg12]
end R7.Core.SpectralCoefficient.Expansion
