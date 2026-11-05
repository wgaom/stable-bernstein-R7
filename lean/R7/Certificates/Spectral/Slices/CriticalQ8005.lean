import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal112
import R7.Certificates.Spectral.Terminal.Terminal113

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8005
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_30 : BiPoly := [[85325503130],[60867352500],[949644427680],[202321650000],[2506263696264],[148765500000],[1925689185480],[0],[32412205980]]
def witness_30 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_31, 170651006260, by norm_num, R7.Core.Certificates.Terminal112.positive_31⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_0, 320410719745228338303600, by norm_num, R7.Core.Certificates.Terminal113.positive_0⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_1, 1599082072749750960351815524835500800, by norm_num, R7.Core.Certificates.Terminal113.positive_1⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_2, 6151579042991253181918258964391448593079776768000, by norm_num, R7.Core.Certificates.Terminal113.positive_2⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_3, 398772494087367546941330042153674234298965854353669345280000, by norm_num, R7.Core.Certificates.Terminal113.positive_3⟩
theorem bound_30 : ordinaryBindings polynomial_30 witness_30 := by
 decide +kernel
theorem positive_30 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_30 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_30 ρ hρ u
def polynomial_31 : BiPoly := [[431861354590],[156272546250],[4537558061340],[435962752500],[11225791621728],[252901350000],[8121384825720],[0],[129648823920]]
def witness_31 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_4, 863722709180, by norm_num, R7.Core.Certificates.Terminal113.positive_4⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_5, 7813962774892808453139900, by norm_num, R7.Core.Certificates.Terminal113.positive_5⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_6, 175271673522007860833122994321952494400, by norm_num, R7.Core.Certificates.Terminal113.positive_6⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_7, 2846397645469865324397054180776946652137976551936000, by norm_num, R7.Core.Certificates.Terminal113.positive_7⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_8, 738064214287650310217734715300500410596540027054078398218240000, by norm_num, R7.Core.Certificates.Terminal113.positive_8⟩
theorem bound_31 : ordinaryBindings polynomial_31 witness_31 := by
 decide +kernel
theorem positive_31 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_31 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_31 ρ hρ u
def polynomial_32 : BiPoly := [[1021512346020],[115115167500],[9144630332760],[139806315000],[20382112615896],[0],[13312373064840],[0],[194473235880]]
def witness_32 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_9, 2043024692040, by norm_num, R7.Core.Certificates.Terminal113.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_10, 37352159637024730390210800, by norm_num, R7.Core.Certificates.Terminal113.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_11, 1522591915773826955000117776368741753600, by norm_num, R7.Core.Certificates.Terminal113.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_12, 40538623216581255762381445290317824768693016206848000, by norm_num, R7.Core.Certificates.Terminal113.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_13, 15767354470097301758128432080958586832821086760206027950612480000, by norm_num, R7.Core.Certificates.Terminal113.positive_13⟩
theorem bound_32 : ordinaryBindings polynomial_32 witness_32 := by
 decide +kernel
theorem positive_32 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_32 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_32 ρ hρ u
def polynomial_33 : BiPoly := [[1179301982860],[-22233573750],[8993205943200],[-130537867500],[17426470232592],[-104135850000],[9963348394440],[0],[129648823920]]
def witness_33 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_14, 2358603965720, by norm_num, R7.Core.Certificates.Terminal113.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_15, 42422328072534689445145500, by norm_num, R7.Core.Certificates.Terminal113.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_16, 1478502683776918413455012524848814272000, by norm_num, R7.Core.Certificates.Terminal113.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_17, 29461214641765396300909867025251122413964164895360000, by norm_num, R7.Core.Certificates.Terminal113.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_18, 7639223659119135485931365371494793927260810727416747730022400000, by norm_num, R7.Core.Certificates.Terminal113.positive_18⟩
theorem bound_33 : ordinaryBindings polynomial_33 witness_33 := by
 decide +kernel
theorem positive_33 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_33 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_33 ρ hρ u
def polynomial_34 : BiPoly := [[589650991430],[0],[3597282377280],[0],[5808823410864],[0],[2846670969840],[0],[32412205980]]
def witness_34 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_19, 1179301982860, by norm_num, R7.Core.Certificates.Terminal113.positive_19⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_20, 8484564480867277226841600, by norm_num, R7.Core.Certificates.Terminal113.positive_20⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_21, 98570673574894001539413387931694284800, by norm_num, R7.Core.Certificates.Terminal113.positive_21⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_22, 561196549886451134474800724016392642772002340864000, by norm_num, R7.Core.Certificates.Terminal113.positive_22⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_23, 36379236340369999563603840372544902468165396098252278333440000, by norm_num, R7.Core.Certificates.Terminal113.positive_23⟩
theorem bound_34 : ordinaryBindings polynomial_34 witness_34 := by
 decide +kernel
theorem positive_34 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_34 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_34 ρ hρ u
def polynomial_35 : BiPoly := [[104484139332],[13815136500],[1055307682392],[12527781000],[2485305691680],[-17851860000],[1708002581904],[0],[25929764784]]
def witness_35 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_24, 208968278664, by norm_num, R7.Core.Certificates.Terminal113.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_25, 440860801704189291918576, by norm_num, R7.Core.Certificates.Terminal113.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_26, 2191314922839545626865438211737295360, by norm_num, R7.Core.Certificates.Terminal113.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_27, 7485402594503061789756943802326197166970078330880, by norm_num, R7.Core.Certificates.Terminal113.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_28, 388189457178015447152431226650049769161482610171547447459840, by norm_num, R7.Core.Certificates.Terminal113.positive_28⟩
theorem bound_35 : ordinaryBindings polynomial_35 witness_35 := by
 decide +kernel
theorem positive_35 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_35 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_35 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8005
