import R7.Certificates.Scalar.Batches.Batch00
import R7.Certificates.Scalar.Batches.Batch01
set_option Elab.async false

namespace R7.Certificates.Scalar
open R7.Core
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_matrix_conditions (row : Fin 11) : MatrixSigns (Paper.rows row) := by
 fin_cases row
 · exact Row01E0.side_conditions
 · exact Row02E0.side_conditions
 · exact Row03E0.side_conditions
 · exact Row04E0.side_conditions
 · exact Row05E0.side_conditions
 · exact Row06E0.side_conditions
 · exact Row07E0.side_conditions
 · exact Row08E0.side_conditions
 · exact Row09E0.side_conditions
 · exact Row10E0.side_conditions
 · exact Row11E0.side_conditions

theorem endpoint_lower_bound (row : Fin 11) (side : Fin 2) (q ρ : ℝ)
 (hq : 0 ≤ q) (hqmax : q ≤ Real.sqrt (5/6 : ℝ)) (hρ : 0 ≤ ρ) :
 Paper.scalarF (Paper.rows row) (Paper.endpoint row side) q ρ ≥
   (1/10000000 : ℝ)*(1+ρ+ρ^2) := by
 have hmargin : ((1/10000000 : ℚ) : ℝ) = (1/10000000 : ℝ) := by norm_num
 rw [← hmargin]
 fin_cases row <;> fin_cases side
 · exact Row01E0.paper_lower q ρ hq hqmax hρ
 · exact Row01E1.paper_lower q ρ hq hqmax hρ
 · exact Row02E0.paper_lower q ρ hq hqmax hρ
 · exact Row02E1.paper_lower q ρ hq hqmax hρ
 · exact Row03E0.paper_lower q ρ hq hqmax hρ
 · exact Row03E1.paper_lower q ρ hq hqmax hρ
 · exact Row04E0.paper_lower q ρ hq hqmax hρ
 · exact Row04E1.paper_lower q ρ hq hqmax hρ
 · exact Row05E0.paper_lower q ρ hq hqmax hρ
 · exact Row05E1.paper_lower q ρ hq hqmax hρ
 · exact Row06E0.paper_lower q ρ hq hqmax hρ
 · exact Row06E1.paper_lower q ρ hq hqmax hρ
 · exact Row07E0.paper_lower q ρ hq hqmax hρ
 · exact Row07E1.paper_lower q ρ hq hqmax hρ
 · exact Row08E0.paper_lower q ρ hq hqmax hρ
 · exact Row08E1.paper_lower q ρ hq hqmax hρ
 · exact Row09E0.paper_lower q ρ hq hqmax hρ
 · exact Row09E1.paper_lower q ρ hq hqmax hρ
 · exact Row10E0.paper_lower q ρ hq hqmax hρ
 · exact Row10E1.paper_lower q ρ hq hqmax hρ
 · exact Row11E0.paper_lower q ρ hq hqmax hρ
 · exact Row11E1.paper_lower q ρ hq hqmax hρ

end R7.Certificates.Scalar
