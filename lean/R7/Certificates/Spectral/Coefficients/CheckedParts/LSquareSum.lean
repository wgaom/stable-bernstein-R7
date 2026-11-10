import R7.Certificates.Spectral.Coefficients.CheckedParts.LSquaresA
import R7.Certificates.Spectral.Coefficients.CheckedParts.LSquaresB
import R7.Certificates.Spectral.Coefficients.CheckedParts.LSquaresC
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct184 : interpretKey p184 = e184.denote := by
  have he : interpretKey p184 = interpretKey p174 + interpretKey p183 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct174,correct183]
  rfl
theorem correct185 : interpretKey p185 = e185.denote := by
  have he : interpretKey p185 = interpretKey p165 + interpretKey p184 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct165,correct184]
  rfl
theorem correct186 : interpretKey p186 = e186.denote := by
  have he : interpretKey p186 = interpretKey p156 + interpretKey p185 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct156,correct185]
  rfl
theorem correct187 : interpretKey p187 = e187.denote := by
  have he : interpretKey p187 = interpretKey p147 + interpretKey p186 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct147,correct186]
  rfl
theorem correct188 : interpretKey p188 = e188.denote := by
  have he : interpretKey p188 = interpretKey p137 + interpretKey p187 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct137,correct187]
  rfl
end R7.Core.SpectralCoefficient.Expansion
