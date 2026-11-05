import R7.Certificates.Spectral.Coefficients.EntryAGroups
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryAg0 : subHom (interpretKey entryAG0) = interpretKey entryAO0 := by
  have hz : ∀ a∈entryAG0, a.exp 0=0 := by
    have hh : entryAG0.all (fun a => a.exp 0 == 0)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 0 hz]
  rw [← gapPower_correct 0,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg1 : subHom (interpretKey entryAG1) = interpretKey entryAO1 := by
  have hz : ∀ a∈entryAG1, a.exp 0=1 := by
    have hh : entryAG1.all (fun a => a.exp 0 == 1)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 1 hz]
  rw [← gapPower_correct 1,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg2 : subHom (interpretKey entryAG2) = interpretKey entryAO2 := by
  have hz : ∀ a∈entryAG2, a.exp 0=2 := by
    have hh : entryAG2.all (fun a => a.exp 0 == 2)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 2 hz]
  rw [← gapPower_correct 2,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg3 : subHom (interpretKey entryAG3) = interpretKey entryAO3 := by
  have hz : ∀ a∈entryAG3, a.exp 0=3 := by
    have hh : entryAG3.all (fun a => a.exp 0 == 3)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 3 hz]
  rw [← gapPower_correct 3,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg4 : subHom (interpretKey entryAG4) = interpretKey entryAO4 := by
  have hz : ∀ a∈entryAG4, a.exp 0=4 := by
    have hh : entryAG4.all (fun a => a.exp 0 == 4)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 4 hz]
  rw [← gapPower_correct 4,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg5 : subHom (interpretKey entryAG5) = interpretKey entryAO5 := by
  have hz : ∀ a∈entryAG5, a.exp 0=5 := by
    have hh : entryAG5.all (fun a => a.exp 0 == 5)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 5 hz]
  rw [← gapPower_correct 5,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg6 : subHom (interpretKey entryAG6) = interpretKey entryAO6 := by
  have hz : ∀ a∈entryAG6, a.exp 0=6 := by
    have hh : entryAG6.all (fun a => a.exp 0 == 6)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 6 hz]
  rw [← gapPower_correct 6,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg7 : subHom (interpretKey entryAG7) = interpretKey entryAO7 := by
  have hz : ∀ a∈entryAG7, a.exp 0=7 := by
    have hh : entryAG7.all (fun a => a.exp 0 == 7)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 7 hz]
  rw [← gapPower_correct 7,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg8 : subHom (interpretKey entryAG8) = interpretKey entryAO8 := by
  have hz : ∀ a∈entryAG8, a.exp 0=8 := by
    have hh : entryAG8.all (fun a => a.exp 0 == 8)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 8 hz]
  rw [← gapPower_correct 8,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg9 : subHom (interpretKey entryAG9) = interpretKey entryAO9 := by
  have hz : ∀ a∈entryAG9, a.exp 0=9 := by
    have hh : entryAG9.all (fun a => a.exp 0 == 9)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 9 hz]
  rw [← gapPower_correct 9,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg10 : subHom (interpretKey entryAG10) = interpretKey entryAO10 := by
  have hz : ∀ a∈entryAG10, a.exp 0=10 := by
    have hh : entryAG10.all (fun a => a.exp 0 == 10)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 10 hz]
  rw [← gapPower_correct 10,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg11 : subHom (interpretKey entryAG11) = interpretKey entryAO11 := by
  have hz : ∀ a∈entryAG11, a.exp 0=11 := by
    have hh : entryAG11.all (fun a => a.exp 0 == 11)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 11 hz]
  rw [← gapPower_correct 11,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryAg12 : subHom (interpretKey entryAG12) = interpretKey entryAO12 := by
  have hz : ∀ a∈entryAG12, a.exp 0=12 := by
    have hh : entryAG12.all (fun a => a.exp 0 == 12)=true := by decide +kernel
    intro a ha; simpa using (List.all_eq_true.mp hh) a ha
  rw [subHom_key_group _ 12 hz]
  rw [← gapPower_correct 12,← interpretKey_mul]
  exact congrArg interpretKey (keyPolyEqual_sound _ _ (by decide +kernel))
theorem entryA_substitution : interpretKey entryAData=subHom (interpretKey p59) := by
  have hr : normalizeKey (entryAG0 ++ entryAG1 ++ entryAG2 ++ entryAG3 ++ entryAG4 ++ entryAG5 ++ entryAG6 ++ entryAG7 ++ entryAG8 ++ entryAG9 ++ entryAG10 ++ entryAG11 ++ entryAG12)=p59 := keyPolyEqual_sound _ _ (by decide +kernel)
  have ho : normalizeKey (entryAO0 ++ entryAO1 ++ entryAO2 ++ entryAO3 ++ entryAO4 ++ entryAO5 ++ entryAO6 ++ entryAO7 ++ entryAO8 ++ entryAO9 ++ entryAO10 ++ entryAO11 ++ entryAO12)=entryAData := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← ho,interpret_normalizeKey,← hr,interpret_normalizeKey]
  simp only [interpretKey_append,map_add,entryAg0,entryAg1,entryAg2,entryAg3,entryAg4,entryAg5,entryAg6,entryAg7,entryAg8,entryAg9,entryAg10,entryAg11,entryAg12]
end R7.Core.SpectralCoefficient.Expansion
