import R7.Certificates.Spectral.Coefficients.CheckedParts.LForms
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct189 : interpretKey p189 = e189.denote := by
  have he : computeKey e189=p189 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e189
theorem correct190 : interpretKey p190 = e190.denote := by
  have he : interpretKey p190 = interpretKey p173 + interpretKey p182 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct173,correct182]
  rfl
theorem correct191 : interpretKey p191 = e191.denote := by
  have he : interpretKey p191 = interpretKey p164 + interpretKey p190 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct164,correct190]
  rfl
theorem correct192 : interpretKey p192 = e192.denote := by
  have he : interpretKey p192 = interpretKey p155 + interpretKey p191 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct155,correct191]
  rfl
theorem correct193 : interpretKey p193 = e193.denote := by
  have he : interpretKey p193 = interpretKey p146 + interpretKey p192 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct146,correct192]
  rfl
theorem correct194 : interpretKey p194 = e194.denote := by
  have he : interpretKey p194 = interpretKey p136 + interpretKey p193 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct136,correct193]
  rfl
theorem correct195 : interpretKey p195 = e195.denote := by
  have he : mulKey p189 p194=p195 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct189,correct194]
  rfl
end R7.Core.SpectralCoefficient.Expansion
