import R7.Spectral.ScaledPacked
import R7.Certificates.Spectral.Coefficients.CheckedParts.QCommon
import R7.Certificates.Spectral.Coefficients.DataParts.CriticalLData
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
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
  have he : interpretKey p315 = interpretKey p312 + interpretKey p314 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct312,correct314]
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
  have he : interpretKey p319 = interpretKey p316 + interpretKey p318 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct316,correct318]
  rfl
theorem correct320 : interpretKey p320 = e320.denote := by
  have he : mulKey p69 p319=p320 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct319]
  rfl
theorem correct321 : interpretKey p321 = e321.denote := by
  have he : interpretKey p321 = interpretKey p315 + interpretKey p320 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct315,correct320]
  rfl
theorem correct322 : interpretKey p322 = e322.denote := by
  have he : interpretKey p322 = interpretKey p321 + interpretKey p249 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct321,correct249]
  rfl
theorem correct323 : interpretKey p323 = e323.denote := by
  have he : computeKey e323=p323 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e323
theorem correct324 : interpretKey p324 = e324.denote := by
  have he : mulKey p323 p83=p324 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct323,correct83]
  rfl
theorem correct325 : interpretKey p325 = e325.denote := by
  have he : interpretKey p325 = interpretKey p322 + interpretKey p324 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct322,correct324]
  rfl
theorem correct326 : interpretKey p326 = e326.denote := by
  have he : interpretKey p326=interpretKey p61*interpretKey p325 :=
    ScaledPacked.Product.multiply 13 1 40 8 4 (by decide) (by decide)
      (by decide) (by decide) p61 p325 p326
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (B := R7.Algebra.KernelPower.fastPow 2 61)
      (by decide +kernel) (by decide +kernel)
  rw [he,correct61,correct325]
  rfl

end R7.Core.SpectralCoefficient.Expansion
