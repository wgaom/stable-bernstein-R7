import R7.Certificates.Spectral.Coefficients.Expanded
import R7.Certificates.Spectral.Coefficients.DataParts.EntryAData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryA_ast : substitute e59 = entryAExpr := by with_unfolding_all rfl
end R7.Core.SpectralCoefficient.Expansion
