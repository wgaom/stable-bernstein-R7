import R7.Certificates.Spectral.Coefficients.CheckedParts.CriticalLEarly
import R7.Certificates.Spectral.Coefficients.CheckedParts.LNegativeVariance
import R7.Certificates.Spectral.Coefficients.CheckedParts.LCorrection
import R7.Certificates.Spectral.Coefficients.CheckedParts.LSmallCorrection
import R7.Spectral.RationalCrossArithmetic
import R7.Certificates.Spectral.Coefficients.CriticalLData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct327 : interpretKey p327 = e327.denote := by
  have he : interpretKey p327 = interpretKey p326 + interpretKey p200 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct326,correct200]
  rfl
theorem correct328 : interpretKey p328 = e328.denote := by
  have he : interpretKey p328 = interpretKey p327 + interpretKey p230 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct327,correct230]
  rfl
theorem correct329 : interpretKey p329 = e329.denote := by
  have he : interpretKey p329 = interpretKey p328 + interpretKey p234 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct328,correct234]
  rfl
theorem correct330 : interpretKey p330 = e330.denote := by
  have he : interpretKey p330 = interpretKey p309 * interpretKey p329 :=
    RationalCrossScale.verifyScale_sound _ _ _ (by decide +kernel)
  rw [he,correct309,correct329]
  rfl
theorem criticalL_raw : interpretKey p330 = e330.denote := correct330
end R7.Core.SpectralCoefficient.Expansion
