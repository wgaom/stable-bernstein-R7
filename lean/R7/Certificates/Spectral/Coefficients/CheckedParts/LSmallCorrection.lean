import R7.Certificates.Spectral.Coefficients.EntryAChecked
import R7.Certificates.Spectral.Coefficients.EntryLData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct232 : interpretKey p232 = e232.denote := by
  have he : computeKey e232=p232 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e232
theorem correct233 : interpretKey p233 = e233.denote := by
  have he : mulKey p232 p57=p233 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct232,correct57]
  rfl
theorem correct234 : interpretKey p234 = e234.denote := by
  have he : negKey p233=p234 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct233]
  rfl
end R7.Core.SpectralCoefficient.Expansion
