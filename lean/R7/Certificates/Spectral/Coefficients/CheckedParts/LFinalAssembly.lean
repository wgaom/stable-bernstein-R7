import R7.Certificates.Spectral.Coefficients.CheckedParts.LCorrection
import R7.Certificates.Spectral.Coefficients.CheckedParts.LNegativeVariance
import R7.Certificates.Spectral.Coefficients.CheckedParts.LSmallCorrection
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct231 : interpretKey p231 = e231.denote := by
  have he : interpretKey p231 = interpretKey p201 + interpretKey p230 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct201,correct230]
  rfl
theorem correct235 : interpretKey p235 = e235.denote := by
  have he : interpretKey p235 = interpretKey p231 + interpretKey p234 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct231,correct234]
  rfl
theorem correct236 : interpretKey p236 = e236.denote := by
  have he : interpretKey p236 = interpretKey p0 * interpretKey p235 :=
    RationalCrossScale.verifyScale_sound _ _ _ (by decide +kernel)
  rw [he,correct0,correct235]
  rfl
end R7.Core.SpectralCoefficient.Expansion
