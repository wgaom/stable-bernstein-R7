import R7.Certificates.Spectral.Slices.Groups
import R7.Certificates.Spectral.Coefficients.Expanded
namespace R7.Core.SpectralCertificateTheorem
open R7.Core.SpectralGrouped R7.Core.SpectralCoefficient
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem groupedEntryQ_checked : normalizeKey (flattenGrouped entryGroups 2) = entryQData := by
 decide +kernel
end R7.Core.SpectralCertificateTheorem
