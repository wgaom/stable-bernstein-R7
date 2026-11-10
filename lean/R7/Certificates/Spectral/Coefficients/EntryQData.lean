import R7.Certificates.Spectral.Coefficients.EntryLData
import R7.Certificates.Spectral.Coefficients.DataParts.EntryQData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryQ_ast : substitute e308 = entryQExpr := by with_unfolding_all rfl
end R7.Core.SpectralCoefficient.Expansion
