import R7.Certificates.Spectral.Coefficients.CheckedParts.ACommon
import R7.Certificates.Spectral.Coefficients.EntryAData
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct56 : interpretKey p56 = e56.denote := by
  have he : powerKey p49 5=p56 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct49]
  rfl
theorem correct57 : interpretKey p57 = e57.denote := by
  have he : mulKey p55 p56=p57 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct55,correct56]
  rfl
theorem correct58 : interpretKey p58 = e58.denote := by
  have he : mulKey p1 p57=p58 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct1,correct57]
  rfl
theorem correct59 : interpretKey p59 = e59.denote := by
  have he : interpretKey p59 = interpretKey p0 * interpretKey p58 :=
    RationalCrossScale.verifyScale_sound _ _ _ (by decide +kernel)
  rw [he,correct0,correct58]
  rfl
theorem entryA_raw : interpretKey p59 = e59.denote := correct59
end R7.Core.SpectralCoefficient.Expansion
