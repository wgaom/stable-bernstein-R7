import R7.Certificates.Spectral.Coefficients.EntryLGroups
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryLg0 : subHom (interpretKey entryLG0) = interpretKey entryLO0 := by
  have hz : ∀ a∈entryLG0, a.exp 0=0 := by
    have hh : entryLG0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPower_correct 0,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg1 : subHom (interpretKey entryLG1) = interpretKey entryLO1 := by
  have hz : ∀ a∈entryLG1, a.exp 0=1 := by
    have hh : entryLG1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPower_correct 1,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg2 : subHom (interpretKey entryLG2) = interpretKey entryLO2 := by
  have hz : ∀ a∈entryLG2, a.exp 0=2 := by
    have hh : entryLG2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  rw [← gapPower_correct 2,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg3 : subHom (interpretKey entryLG3) = interpretKey entryLO3 := by
  have hz : ∀ a∈entryLG3, a.exp 0=3 := by
    have hh : entryLG3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  rw [← gapPower_correct 3,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg4 : subHom (interpretKey entryLG4) = interpretKey entryLO4 := by
  have hz : ∀ a∈entryLG4, a.exp 0=4 := by
    have hh : entryLG4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  rw [← gapPower_correct 4,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg5 : subHom (interpretKey entryLG5) = interpretKey entryLO5 := by
  have hz : ∀ a∈entryLG5, a.exp 0=5 := by
    have hh : entryLG5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  rw [← gapPower_correct 5,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg6 : subHom (interpretKey entryLG6) = interpretKey entryLO6 := by
  have hz : ∀ a∈entryLG6, a.exp 0=6 := by
    have hh : entryLG6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  rw [← gapPower_correct 6,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg7 : subHom (interpretKey entryLG7) = interpretKey entryLO7 := by
  have hz : ∀ a∈entryLG7, a.exp 0=7 := by
    have hh : entryLG7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  rw [← gapPower_correct 7,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg8 : subHom (interpretKey entryLG8) = interpretKey entryLO8 := by
  have hz : ∀ a∈entryLG8, a.exp 0=8 := by
    have hh : entryLG8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  rw [← gapPower_correct 8,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg9 : subHom (interpretKey entryLG9) = interpretKey entryLO9 := by
  have hz : ∀ a∈entryLG9, a.exp 0=9 := by
    have hh : entryLG9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  rw [← gapPower_correct 9,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg10 : subHom (interpretKey entryLG10) = interpretKey entryLO10 := by
  have hz : ∀ a∈entryLG10, a.exp 0=10 := by
    have hh : entryLG10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  rw [← gapPower_correct 10,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg11 : subHom (interpretKey entryLG11) = interpretKey entryLO11 := by
  have hz : ∀ a∈entryLG11, a.exp 0=11 := by
    have hh : entryLG11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPower_correct 11,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryLg12 : subHom (interpretKey entryLG12) = interpretKey entryLO12 := by
  have hz : ∀ a∈entryLG12, a.exp 0=12 := by
    have hh : entryLG12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPower_correct 12,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryL_substitution : interpretKey entryLData=subHom (interpretKey p236) := by
  have hr : normalizeKey (entryLG0 ++ entryLG1 ++ entryLG2 ++ entryLG3 ++ entryLG4 ++ entryLG5 ++ entryLG6 ++ entryLG7 ++ entryLG8 ++ entryLG9 ++ entryLG10 ++ entryLG11 ++ entryLG12)=p236 := keyPolyEqual_sound _ _ (by decide +kernel)
  have ho : normalizeKey (entryLO0 ++ entryLO1 ++ entryLO2 ++ entryLO3 ++ entryLO4 ++ entryLO5 ++ entryLO6 ++ entryLO7 ++ entryLO8 ++ entryLO9 ++ entryLO10 ++ entryLO11 ++ entryLO12)=entryLData := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,interpret_normalizeKey,← hr,interpret_normalizeKey]
  simp only [interpretKey_append,map_add,entryLg0,entryLg1,entryLg2,entryLg3,entryLg4,entryLg5,entryLg6,entryLg7,entryLg8,entryLg9,entryLg10,entryLg11,entryLg12]
end R7.Core.SpectralCoefficient.Expansion
