import R7.Certificates.Spectral.Coefficients.EntryAData
import R7.Certificates.Spectral.Coefficients.DataParts.EntryLData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryL_ast : substitute e236 = entryLExpr := by with_unfolding_all rfl
end R7.Core.SpectralCoefficient.Expansion
