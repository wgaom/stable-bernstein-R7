import R7.Certificates.Spectral.Coefficients.EntryAChecked
import R7.Certificates.Spectral.Coefficients.EntryASubstituted
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
theorem entryA_source : interpretKey entryAData = entryAExpr.denote := by
 rw [entryA_substitution,entryA_raw,subHom_expr,entryA_ast]
end R7.Core.SpectralCoefficient.Expansion
