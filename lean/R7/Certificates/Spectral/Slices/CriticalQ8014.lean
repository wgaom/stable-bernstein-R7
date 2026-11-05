import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal121

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8014
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_84 : BiPoly := [[20857486630],[0],[309797598330],[0],[1216344314544],[0],[1339609868160],[0],[32412205980]]
def witness_84 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal121.polynomial_13, 41714973260, by norm_num, R7.Core.Certificates.Terminal121.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal121.polynomial_14, 25846397060696341311600, by norm_num, R7.Core.Certificates.Terminal121.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_15, 62876236232449495271973543831820800, by norm_num, R7.Core.Certificates.Terminal121.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_16, 168459253059497366950294044791106886201491456000, by norm_num, R7.Core.Certificates.Terminal121.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_17, 10920272018802747705721150002673404935518321710164213760000, by norm_num, R7.Core.Certificates.Terminal121.positive_17⟩
theorem bound_84 : ordinaryBindings polynomial_84 witness_84 := by
 decide +kernel
theorem positive_84 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_84 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_84 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8014
