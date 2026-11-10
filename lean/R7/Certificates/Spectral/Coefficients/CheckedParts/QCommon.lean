import R7.Certificates.Spectral.Coefficients.CheckedParts.LCommon
import R7.Certificates.Spectral.Coefficients.DataParts.EntryQData
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct237 : interpretKey p237 = e237.denote := by
  have he : mulKey p55 p49=p237 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct55,correct49]
  rfl
theorem correct238 : interpretKey p238 = e238.denote := by
  have he : computeKey e238=p238 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e238
theorem correct239 : interpretKey p239 = e239.denote := by
  have he : powerKey p49 4=p239 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct49]
  rfl
theorem correct240 : interpretKey p240 = e240.denote := by
  have he : mulKey p238 p239=p240 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct238,correct239]
  rfl
theorem correct241 : interpretKey p241 = e241.denote := by
  have he : computeKey e241=p241 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e241
theorem correct242 : interpretKey p242 = e242.denote := by
  have he : computeKey e242=p242 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e242
theorem correct243 : interpretKey p243 = e243.denote := by
  have he : mulKey p242 p7=p243 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct7]
  rfl
theorem correct244 : interpretKey p244 = e244.denote := by
  have he : mulKey p243 p49=p244 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct243,correct49]
  rfl
theorem correct245 : interpretKey p245 = e245.denote := by
  have he : mulKey p69 p71=p245 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct71]
  rfl
theorem correct246 : interpretKey p246 = e246.denote := by
  have he : interpretKey p246 = interpretKey p244 + interpretKey p245 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct244,correct245]
  rfl
theorem correct247 : interpretKey p247 = e247.denote := by
  have he : computeKey e247=p247 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e247
theorem correct248 : interpretKey p248 = e248.denote := by
  have he : mulKey p247 p100=p248 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct247,correct100]
  rfl
theorem correct249 : interpretKey p249 = e249.denote := by
  have he : mulKey p248 p6=p249 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct6]
  rfl
end R7.Core.SpectralCoefficient.Expansion
