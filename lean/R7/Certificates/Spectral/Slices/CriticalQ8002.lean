import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal110
import R7.Certificates.Spectral.Terminal.Terminal111

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8002
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_12 : BiPoly := [[333356659880],[595166587500],[4127643512910],[1929123465000],[10818578033952],[1606667400000],[8205110442480],[0],[129648823920]]
def witness_12 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_5, 666713319760, by norm_num, R7.Core.Certificates.Terminal110.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_6, 5149686551679713879953200, by norm_num, R7.Core.Certificates.Terminal110.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_7, 108943386437041988148100800897542092800, by norm_num, R7.Core.Certificates.Terminal110.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_8, 1774491736825434314155637132054520789565266444288000, by norm_num, R7.Core.Certificates.Terminal110.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_9, 460121533470351426346980324018300707372653205166758803537920000, by norm_num, R7.Core.Certificates.Terminal110.positive_9⟩
theorem bound_12 : ordinaryBindings polynomial_12 witness_12 := by
 decide +kernel
theorem positive_12 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_12 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_12 ρ hρ u
def polynomial_13 : BiPoly := [[573858693060],[672950561250],[5682112839150],[1899819315000],[13192107701184],[1309136400000],[8874915376560],[0],[129648823920]]
def witness_13 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_10, 1147717386120, by norm_num, R7.Core.Certificates.Terminal110.positive_10⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_11, 12590056932889570003633500, by norm_num, R7.Core.Certificates.Terminal110.positive_11⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_12, 328036302270272667401291854267504128000, by norm_num, R7.Core.Certificates.Terminal110.positive_12⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_13, 5801011526750093345286116037840183760080948879360000, by norm_num, R7.Core.Certificates.Terminal110.positive_13⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_14, 1504188643979026443933126840421260082822356932413331924582400000, by norm_num, R7.Core.Certificates.Terminal110.positive_14⟩
theorem bound_13 : ordinaryBindings polynomial_13 witness_13 := by
 decide +kernel
theorem positive_13 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_13 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_13 ρ hρ u
def polynomial_14 : BiPoly := [[611337538152],[511727382000],[4988850665070],[1222783902000],[10093030235424],[687296610000],[5927773666608],[0],[77789294352]]
def witness_14 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_15, 1222675076304, by norm_num, R7.Core.Certificates.Terminal110.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_16, 11937621821678872871002560, by norm_num, R7.Core.Certificates.Terminal110.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_17, 239145411620566490450465838911797370880, by norm_num, R7.Core.Certificates.Terminal110.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_18, 2829560693421307969553395116742247643897968095150080, by norm_num, R7.Core.Certificates.Terminal110.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_19, 440219059334798711184865013434444210570515033616668633472696320, by norm_num, R7.Core.Certificates.Terminal110.positive_19⟩
theorem bound_14 : ordinaryBindings polynomial_14 witness_14 := by
 decide +kernel
theorem positive_14 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_14 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_14 ρ hρ u
def polynomial_15 : BiPoly := [[381794060928],[245680459500],[2564721264456],[502359436500],[4431356958912],[235049490000],[2243846529168],[0],[25929764784]]
def witness_15 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_20, 763588121856, by norm_num, R7.Core.Certificates.Terminal110.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_21, 3856422498640073918850672, by norm_num, R7.Core.Certificates.Terminal110.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_22, 33985666432707599985672834398479177728, by norm_num, R7.Core.Certificates.Terminal110.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_23, 152304178689507679566393291670447173617595615940608, by norm_num, R7.Core.Certificates.Terminal110.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_24, 7898423058078478999836442328500403312003729369939132707897344, by norm_num, R7.Core.Certificates.Terminal110.positive_24⟩
theorem bound_15 : ordinaryBindings polynomial_15 witness_15 := by
 decide +kernel
theorem positive_15 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_15 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_15 ρ hρ u
def polynomial_16 : BiPoly := [[109084017408],[62805531000],[591858753336],[105467727000],[852184030560],[41654340000],[368392713744],[0],[3704252112]]
def witness_16 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_25, 218168034816, by norm_num, R7.Core.Certificates.Terminal110.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_26, 254304787483733647292352, by norm_num, R7.Core.Certificates.Terminal110.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_27, 431002178218146203710863962380554240, by norm_num, R7.Core.Certificates.Terminal110.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_28, 317114883948444897728543879467430636525570949120, by norm_num, R7.Core.Certificates.Terminal110.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_29, 2349346957225323823053165336403806741126701060567209082880, by norm_num, R7.Core.Certificates.Terminal110.positive_29⟩
theorem bound_16 : ordinaryBindings polynomial_16 witness_16 := by
 decide +kernel
theorem positive_16 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_16 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_16 ρ hρ u
def polynomial_17 : BiPoly := [[15992093848],[50574105000],[275162699148],[194617266000],[844504836672],[202321080000],[753530550840],[0],[12964882392]]
def witness_17 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_30, 31984187696, by norm_num, R7.Core.Certificates.Terminal110.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_31, 15043970736424197566016, by norm_num, R7.Core.Certificates.Terminal110.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_0, 24197982837046847127011561859477504, by norm_num, R7.Core.Certificates.Terminal111.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_1, 35852031491463840484332452583750856265016606720, by norm_num, R7.Core.Certificates.Terminal111.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_2, 929634743602218087600037132754492763410473380103433748480, by norm_num, R7.Core.Certificates.Terminal111.positive_2⟩
theorem bound_17 : ordinaryBindings polynomial_17 witness_17 := by
 decide +kernel
theorem positive_17 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_17 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_17 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8002
