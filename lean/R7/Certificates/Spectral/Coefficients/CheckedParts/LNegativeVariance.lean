import R7.Certificates.Spectral.Coefficients.CheckedParts.LNegativeClosed
import R7.Spectral.Kronecker.Core
import R7.Certificates.Spectral.Coefficients.CheckedParts.LLeading
import R7.Certificates.Spectral.Coefficients.CheckedParts.LSquareSum
import R7.Certificates.Spectral.Coefficients.CheckedParts.LVariance
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem correct198 : interpretKey p198 = e198.denote := by
  have he : interpretKey p198 = interpretKey p188 + interpretKey p197 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct188,correct197]
  rfl
theorem correct201 : interpretKey p201 = e201.denote := by
  have he : interpretKey p201 = interpretKey p107 + interpretKey p200 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct107,correct200]
  rfl
end R7.Core.SpectralCoefficient.Expansion
