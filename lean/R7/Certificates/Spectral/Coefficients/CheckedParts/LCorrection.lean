import R7.Certificates.Spectral.Coefficients.CheckedParts.LCorrectionClosed
import R7.Spectral.Kronecker.Core
import R7.Certificates.Spectral.Coefficients.CheckedParts.LMean
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem correct203 : interpretKey p203 = e203.denote := by
  have he : mulKey p136 p6=p203 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct136,correct6]
  rfl
theorem correct204 : interpretKey p204 = e204.denote := by
  have he : mulKey p146 p26=p204 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct146,correct26]
  rfl
theorem correct205 : interpretKey p205 = e205.denote := by
  have he : mulKey p155 p31=p205 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct155,correct31]
  rfl
theorem correct206 : interpretKey p206 = e206.denote := by
  have he : mulKey p164 p36=p206 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct164,correct36]
  rfl
theorem correct207 : interpretKey p207 = e207.denote := by
  have he : mulKey p173 p40=p207 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct173,correct40]
  rfl
theorem correct208 : interpretKey p208 = e208.denote := by
  have he : mulKey p182 p43=p208 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct182,correct43]
  rfl
theorem correct209 : interpretKey p209 = e209.denote := by
  have he : interpretKey p209 = interpretKey p207 + interpretKey p208 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct207,correct208]
  rfl
theorem correct210 : interpretKey p210 = e210.denote := by
  have he : interpretKey p210 = interpretKey p206 + interpretKey p209 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct206,correct209]
  rfl
theorem correct211 : interpretKey p211 = e211.denote := by
  have he : interpretKey p211 = interpretKey p205 + interpretKey p210 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct205,correct210]
  rfl
theorem correct212 : interpretKey p212 = e212.denote := by
  have he : interpretKey p212 = interpretKey p204 + interpretKey p211 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct204,correct211]
  rfl
theorem correct213 : interpretKey p213 = e213.denote := by
  have he : interpretKey p213 = interpretKey p203 + interpretKey p212 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct203,correct212]
  rfl
theorem correct214 : interpretKey p214 = e214.denote := by
  have he : mulKey p108 p6=p214 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct108,correct6]
  rfl
theorem correct215 : interpretKey p215 = e215.denote := by
  have he : mulKey p138 p26=p215 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct26]
  rfl
theorem correct216 : interpretKey p216 = e216.denote := by
  have he : mulKey p138 p31=p216 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct31]
  rfl
theorem correct217 : interpretKey p217 = e217.denote := by
  have he : mulKey p138 p36=p217 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct36]
  rfl
theorem correct218 : interpretKey p218 = e218.denote := by
  have he : mulKey p138 p40=p218 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct40]
  rfl
theorem correct219 : interpretKey p219 = e219.denote := by
  have he : mulKey p138 p43=p219 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct43]
  rfl
theorem correct220 : interpretKey p220 = e220.denote := by
  have he : interpretKey p220 = interpretKey p218 + interpretKey p219 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct218,correct219]
  rfl
theorem correct221 : interpretKey p221 = e221.denote := by
  have he : interpretKey p221 = interpretKey p217 + interpretKey p220 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct217,correct220]
  rfl
theorem correct222 : interpretKey p222 = e222.denote := by
  have he : interpretKey p222 = interpretKey p216 + interpretKey p221 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct216,correct221]
  rfl
theorem correct223 : interpretKey p223 = e223.denote := by
  have he : interpretKey p223 = interpretKey p215 + interpretKey p222 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct215,correct222]
  rfl
theorem correct224 : interpretKey p224 = e224.denote := by
  have he : interpretKey p224 = interpretKey p214 + interpretKey p223 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct214,correct223]
  rfl
theorem correct225 : interpretKey p225 = e225.denote := by
  have he : mulKey p195 p224=p225 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct195,correct224]
  rfl
theorem correct226 : interpretKey p226 = e226.denote := by
  have he : negKey p225=p226 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct225]
  rfl
theorem correct227 : interpretKey p227 = e227.denote := by
  have he : interpretKey p227 = interpretKey p213 + interpretKey p226 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct213,correct226]
  rfl
end R7.Core.SpectralCoefficient.Expansion
