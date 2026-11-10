import R7.Certificates.Spectral.Coefficients.CriticalQ8Checked
import R7.Certificates.Spectral.Coefficients.CriticalQ8Substituted
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
theorem criticalQ8_source : interpretKey criticalQ8Data = criticalQ8Expr.denote := by
 rw [criticalQ8_substitution,criticalQ8_raw,subHom_expr,criticalQ8_ast]
end R7.Core.SpectralCoefficient.Expansion
