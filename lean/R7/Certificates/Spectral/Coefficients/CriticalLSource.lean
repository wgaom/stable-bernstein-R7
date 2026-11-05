import R7.Certificates.Spectral.Coefficients.CriticalLChecked
import R7.Certificates.Spectral.Coefficients.CriticalLSubstituted
namespace R7.Core.SpectralCoefficient.Expansion
theorem criticalL_source : interpretKey criticalLData = criticalLExpr.denote := by
 rw [criticalL_substitution,criticalL_raw,subHom_expr,criticalL_ast]
end R7.Core.SpectralCoefficient.Expansion
