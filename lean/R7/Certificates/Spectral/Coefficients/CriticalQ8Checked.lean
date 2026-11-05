import R7.Certificates.Spectral.Coefficients.CriticalQ8Data
import R7.Certificates.Spectral.Coefficients.CriticalLChecked
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct331 : interpretKey p331 = e331.denote := by
  have he : computeKey e331=p331 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e331
theorem correct332 : interpretKey p332 = e332.denote := by
  have he : mulKey p331 p306=p332 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct331,correct306]
  rfl
theorem criticalQ8_raw : interpretKey p332 = e332.denote := correct332
end R7.Core.SpectralCoefficient.Expansion
