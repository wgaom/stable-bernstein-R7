import R7.Certificates.Spectral.Coefficients.CriticalLData
import R7.Certificates.Spectral.Coefficients.EntryQChecked
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct309 : interpretKey p309 = e309.denote := by
  have he : computeKey e309=p309 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e309
theorem correct310 : interpretKey p310 = e310.denote := by
  have he : computeKey e310=p310 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e310
theorem correct311 : interpretKey p311 = e311.denote := by
  have he : mulKey p310 p7=p311 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct310,correct7]
  rfl
theorem correct312 : interpretKey p312 = e312.denote := by
  have he : mulKey p311 p49=p312 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct311,correct49]
  rfl
theorem correct313 : interpretKey p313 = e313.denote := by
  have he : computeKey e313=p313 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e313
theorem correct314 : interpretKey p314 = e314.denote := by
  have he : mulKey p313 p66=p314 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct313,correct66]
  rfl
theorem correct315 : interpretKey p315 = e315.denote := by
  have he : addKey p312 p314=p315 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct312,correct314]
  rfl
theorem correct316 : interpretKey p316 = e316.denote := by
  have he : mulKey p108 p71=p316 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct108,correct71]
  rfl
theorem correct317 : interpretKey p317 = e317.denote := by
  have he : mulKey p241 p83=p317 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct241,correct83]
  rfl
theorem correct318 : interpretKey p318 = e318.denote := by
  have he : negKey p317=p318 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct317]
  rfl
theorem correct319 : interpretKey p319 = e319.denote := by
  have he : addKey p316 p318=p319 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct316,correct318]
  rfl
theorem correct320 : interpretKey p320 = e320.denote := by
  have he : mulKey p69 p319=p320 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct319]
  rfl
theorem correct321 : interpretKey p321 = e321.denote := by
  have he : addKey p315 p320=p321 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct315,correct320]
  rfl
theorem correct322 : interpretKey p322 = e322.denote := by
  have he : addKey p321 p249=p322 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct321,correct249]
  rfl
theorem correct323 : interpretKey p323 = e323.denote := by
  have he : computeKey e323=p323 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e323
theorem correct324 : interpretKey p324 = e324.denote := by
  have he : mulKey p323 p83=p324 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct323,correct83]
  rfl
theorem correct325 : interpretKey p325 = e325.denote := by
  have he : addKey p322 p324=p325 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct322,correct324]
  rfl
theorem correct326 : interpretKey p326 = e326.denote := by
  have he : mulKey p61 p325=p326 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct61,correct325]
  rfl
theorem correct327 : interpretKey p327 = e327.denote := by
  have he : addKey p326 p200=p327 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct326,correct200]
  rfl
theorem correct328 : interpretKey p328 = e328.denote := by
  have he : addKey p327 p230=p328 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct327,correct230]
  rfl
theorem correct329 : interpretKey p329 = e329.denote := by
  have he : addKey p328 p234=p329 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct328,correct234]
  rfl
theorem correct330 : interpretKey p330 = e330.denote := by
  have he : mulKey p309 p329=p330 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct309,correct329]
  rfl
theorem criticalL_raw : interpretKey p330 = e330.denote := correct330
end R7.Core.SpectralCoefficient.Expansion
