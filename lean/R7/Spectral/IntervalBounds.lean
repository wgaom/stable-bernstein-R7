import R7.Spectral.CertificateTheorem
import R7.Certificates.Spectral.Coefficients.All

namespace R7.Core.SpectralCertificateTheorem
open R7.Core.SpectralCoefficient R7.Core.SpectralSource

theorem entry_chart : ChartCertificate (12481/5000) (1/1000000000) :=
 entry_chart_of_sources
   Expansion.entryA_source
   Expansion.entryL_source
   Expansion.entryQ_source

theorem critical_chart : ChartCertificate (5/2) 0 :=
 critical_chart_of_sources
   Expansion.criticalL_source
   Expansion.criticalQ8_source

theorem scalar_interval_bound
 (σ : ℝ) (hσl : 12481/5000 ≤ σ) (hσr : σ ≤ 5/2)
 (l : Spectrum) (i : Fin 6) (R : BasisMatrix)
 (hl : Normalized l) (hR : IsTraceFreeOrthonormalBasis R)
 (ρ : ℝ) (hρ : 0 ≤ ρ) :
 (5/2-σ)/3800000+(ρ+ρ^2)/100000000 ≤ R7.Core.Endpoint.scalar l i R σ ρ :=
 scalar_interval_of_charts entry_chart critical_chart σ hσl hσr l i R hl hR ρ hρ

end R7.Core.SpectralCertificateTheorem
