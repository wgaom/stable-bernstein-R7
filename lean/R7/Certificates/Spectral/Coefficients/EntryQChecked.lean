import R7.Certificates.Spectral.Coefficients.CheckedParts.QFinish
import R7.Certificates.Spectral.Coefficients.EntryQData
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem entryQ_raw : interpretKey p308 = e308.denote := correct308
end R7.Core.SpectralCoefficient.Expansion
