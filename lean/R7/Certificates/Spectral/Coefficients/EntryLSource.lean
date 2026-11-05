import R7.Certificates.Spectral.Coefficients.EntryLChecked
import R7.Certificates.Spectral.Coefficients.EntryLSubstituted
namespace R7.Core.SpectralCoefficient.Expansion
theorem entryL_source : interpretKey entryLData = entryLExpr.denote := by
 rw [entryL_substitution,entryL_raw,subHom_expr,entryL_ast]
end R7.Core.SpectralCoefficient.Expansion
