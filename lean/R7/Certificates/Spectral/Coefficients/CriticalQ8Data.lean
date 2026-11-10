import R7.Certificates.Spectral.Coefficients.CriticalLData
import R7.Certificates.Spectral.Coefficients.DataParts.CriticalQ8Data
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem criticalQ8_ast : substitute e332 = criticalQ8Expr := by with_unfolding_all rfl
end R7.Core.SpectralCoefficient.Expansion
