import R7.Certificates.Spectral.Coefficients.EntryQChecked
import R7.Certificates.Spectral.Coefficients.EntryQSubstituted
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
theorem entryQ_source : interpretKey entryQData = entryQExpr.denote := by
 rw [entryQ_substitution,entryQ_raw,subHom_expr,entryQ_ast]
end R7.Core.SpectralCoefficient.Expansion
