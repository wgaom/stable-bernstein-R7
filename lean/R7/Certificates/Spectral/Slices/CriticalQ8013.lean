import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal120
import R7.Certificates.Spectral.Terminal.Terminal121

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8013
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_78 : BiPoly := [[291199864680],[1598152500],[4253320328520],[1425915000],[13613542382112],[-119012400000],[12726293747520],[0],[259297647840]]
def witness_78 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_15, 582399729360, by norm_num, R7.Core.Certificates.Terminal120.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_16, 4954262662331455322444400, by norm_num, R7.Core.Certificates.Terminal120.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_17, 134890128267373907838532923043349145600, by norm_num, R7.Core.Certificates.Terminal120.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_18, 3433232620007159736032648345195794792195228237824000, by norm_num, R7.Core.Certificates.Terminal120.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_19, 1780458285710834087024842018710275907751088544279422639800320000, by norm_num, R7.Core.Certificates.Terminal120.positive_19⟩
theorem bound_78 : ordinaryBindings polynomial_78 witness_78 := by
 decide +kernel
theorem positive_78 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_78 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_78 ρ hρ u
def polynomial_79 : BiPoly := [[9979358126],[16003390500],[269366708016],[93729267000],[1005626974080],[151740810000],[1121923264584],[0],[25929764784]]
def witness_79 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_20, 19958716252, by norm_num, R7.Core.Certificates.Terminal120.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_21, 10496318878557865502064, by norm_num, R7.Core.Certificates.Terminal120.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_22, 20935421960769867032293519801002240, by norm_num, R7.Core.Certificates.Terminal120.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_23, 46734193291264397516974121424804650881393336320, by norm_num, R7.Core.Certificates.Terminal120.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_24, 2423613278824953259137225231920479081007534985925208309760, by norm_num, R7.Core.Certificates.Terminal120.positive_24⟩
theorem bound_79 : ordinaryBindings polynomial_79 witness_79 := by
 decide +kernel
theorem positive_79 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_79 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_79 ρ hρ u
def polynomial_80 : BiPoly := [[61074509260],[53344635000],[1310952491160],[312430890000],[4973882332992],[505802700000],[5525890706160],[0],[129648823920]]
def witness_80 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_25, 122149018520, by norm_num, R7.Core.Certificates.Terminal120.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_26, 317417470159802727566400, by norm_num, R7.Core.Certificates.Terminal120.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_27, 3145670954422634038264923553181337600, by norm_num, R7.Core.Certificates.Terminal120.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_28, 34684060849601408477884930476655668833994719232000, by norm_num, R7.Core.Certificates.Terminal120.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_29, 8993495395841077219866597130778744958256826127838811258880000, by norm_num, R7.Core.Certificates.Terminal120.positive_29⟩
theorem bound_80 : ordinaryBindings polynomial_80 witness_80 := by
 decide +kernel
theorem positive_80 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_80 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_80 ρ hρ u
def polynomial_81 : BiPoly := [[175589448690],[53344635000],[3138479248680],[312430890000],[11103563633952],[505802700000],[11554135112880],[0],[259297647840]]
def witness_81 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_30, 351178897380, by norm_num, R7.Core.Certificates.Terminal120.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_31, 2201489713919623215916800, by norm_num, R7.Core.Certificates.Terminal120.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_0, 48854482608853576072957470372574387200, by norm_num, R7.Core.Certificates.Terminal121.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_1, 1128379364725157269976508001085057836342537654272000, by norm_num, R7.Core.Certificates.Terminal121.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_2, 585172230288853496357968753476591329467959364578721455144960000, by norm_num, R7.Core.Certificates.Terminal121.positive_2⟩
theorem bound_81 : ordinaryBindings polynomial_81 witness_81 := by
 decide +kernel
theorem positive_81 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_81 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_81 ρ hρ u
def polynomial_82 : BiPoly := [[72252227890],[26672317500],[1275071442240],[156215445000],[4919629795584],[252901350000],[5442165089400],[0],[129648823920]]
def witness_82 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal121.polynomial_3, 144504455780, by norm_num, R7.Core.Certificates.Terminal121.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal121.polynomial_4, 367795597162201002044400, by norm_num, R7.Core.Certificates.Terminal121.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_5, 3615309976402395797924364241683859200, by norm_num, R7.Core.Certificates.Terminal121.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_6, 39326703609131279630037759204855327700410024960000, by norm_num, R7.Core.Certificates.Terminal121.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_7, 10197321743148579553838096372203295180208715675683690086400000, by norm_num, R7.Core.Certificates.Terminal121.positive_7⟩
theorem bound_82 : ordinaryBindings polynomial_82 witness_82 := by
 decide +kernel
theorem positive_82 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_82 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_82 ρ hρ u
def polynomial_83 : BiPoly := [[320093904470],[0],[5688622133160],[0],[20942823225120],[0],[22438465291680],[0],[518595295680]]
def witness_83 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal121.polynomial_8, 640187808940, by norm_num, R7.Core.Certificates.Terminal121.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal121.polynomial_9, 7283573078630578636900800, by norm_num, R7.Core.Certificates.Terminal121.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_10, 305077166866006524483021171395016192000, by norm_num, R7.Core.Certificates.Terminal121.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_11, 13690926840013910241721393419627374542247205765120000, by norm_num, R7.Core.Certificates.Terminal121.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_12, 14200100505460523674236972585266529232317588650832414061363200000, by norm_num, R7.Core.Certificates.Terminal121.positive_12⟩
theorem bound_83 : ordinaryBindings polynomial_83 witness_83 := by
 decide +kernel
theorem positive_83 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_83 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_83 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8013
