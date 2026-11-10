import R7.Certificates.Spectral.Coefficients.EntryQData
import R7.Certificates.Spectral.Coefficients.DataParts.CriticalLData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem criticalL_ast : substitute e330 = criticalLExpr := by with_unfolding_all rfl
end R7.Core.SpectralCoefficient.Expansion
