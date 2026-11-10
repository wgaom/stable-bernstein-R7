import R7.Certificates.Spectral.Coefficients.Expanded
import R7.Certificates.Spectral.Slices.Groups
set_option Elab.async false
namespace R7.Core.SpectralCertificateTheorem
open R7.Core.SpectralGrouped R7.Core.SpectralCoefficient
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem groupedEntryA_checked : normalizeKey (flattenGrouped entryGroups 0) = entryAData := by
 exact keyPolyEqual_sound _ _ (by decide +kernel)
end R7.Core.SpectralCertificateTheorem
