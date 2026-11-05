import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal117
import R7.Certificates.Spectral.Terminal.Terminal118

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8010
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_60 : BiPoly := [[863722709180],[373412445000],[10974404978040],[1478890455000],[32476638028512],[1249630200000],[27796904764320],[0],[518595295680]]
def witness_60 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_21, 1727445418360, by norm_num, R7.Core.Certificates.Terminal117.positive_21⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_22, 37775934343003870800628800, by norm_num, R7.Core.Certificates.Terminal117.positive_22⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_23, 2449892566490270334357129848504856691200, by norm_num, R7.Core.Certificates.Terminal117.positive_23⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_24, 136139870728365516150673657761974239893800222035968000, by norm_num, R7.Core.Certificates.Terminal117.positive_24⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_25, 141202993028427383622548841956516315996537155891184953110036480000, by norm_num, R7.Core.Certificates.Terminal117.positive_25⟩
theorem bound_60 : ordinaryBindings polynomial_60 witness_60 := by
 decide +kernel
theorem positive_60 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_60 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_60 ρ hρ u
def polynomial_61 : BiPoly := [[2043024692040],[313331261250],[22245477842700],[859732335000],[59297148319392],[535555800000],[45714186750960],[0],[777892943520]]
def witness_61 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_26, 4086049384080, by norm_num, R7.Core.Certificates.Terminal117.positive_26⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_27, 181694065596182728496869500, by norm_num, R7.Core.Certificates.Terminal117.positive_27⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_28, 21544859751554106655155619952938286688000, by norm_num, R7.Core.Certificates.Terminal117.positive_28⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_29, 1969759370916968182434762279762182835220203478440960000, by norm_num, R7.Core.Certificates.Terminal117.positive_29⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_30, 3064523830137407721896723180351340262539726422435562469869158400000, by norm_num, R7.Core.Certificates.Terminal117.positive_30⟩
theorem bound_61 : ordinaryBindings polynomial_61 witness_61 := by
 decide +kernel
theorem positive_61 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_61 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_61 ρ hρ u
def polynomial_62 : BiPoly := [[2358603965720],[0],[22081875116100],[0],[51342008264160],[0],[34494954105120],[0],[518595295680]]
def witness_62 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_31, 4717207931440, by norm_num, R7.Core.Certificates.Terminal117.positive_31⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_0, 208329592877468981680368000, by norm_num, R7.Core.Certificates.Terminal118.positive_0⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_1, 21392119358368201463395026999260021760000, by norm_num, R7.Core.Certificates.Terminal118.positive_1⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_2, 1475840350956320422988418956000635445624825054822400000, by norm_num, R7.Core.Certificates.Terminal118.positive_2⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_3, 1530727726361335921049003595405732898383389423307789475774464000000, by norm_num, R7.Core.Certificates.Terminal118.positive_3⟩
theorem bound_62 : ordinaryBindings polynomial_62 witness_62 := by
 decide +kernel
theorem positive_62 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_62 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_62 ρ hρ u
def polynomial_63 : BiPoly := [[261210348330],[43999743750],[3187226781240],[122364195000],[8963539798752],[14876550000],[7284128658120],[0],[129648823920]]
def witness_63 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_4, 522420696660, by norm_num, R7.Core.Certificates.Terminal118.positive_4⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_5, 3328210493487554773254300, by norm_num, R7.Core.Certificates.Terminal118.positive_5⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_6, 59657272230884168564293846331737267200, by norm_num, R7.Core.Certificates.Terminal118.positive_6⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_7, 869101756072444599681871144473536639290113779328000, by norm_num, R7.Core.Certificates.Terminal118.positive_7⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_8, 225356041083198321336219600051956865693985030345723215851520000, by norm_num, R7.Core.Certificates.Terminal118.positive_8⟩
theorem bound_63 : ordinaryBindings polynomial_63 witness_63 := by
 decide +kernel
theorem positive_63 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_63 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_63 ρ hρ u
def polynomial_64 : BiPoly := [[1143809903055],[-172659491250],[12063811568190],[-816303712500],[31476805683408],[-773580600000],[23610623926320],[0],[388946471760]]
def witness_64 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_9, 2287619806110, by norm_num, R7.Core.Certificates.Terminal118.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_10, 55165017261222056860719300, by norm_num, R7.Core.Certificates.Terminal118.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_11, 3471312698243151605901337671034223248800, by norm_num, R7.Core.Certificates.Terminal118.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_12, 163886705065022631994141929974172003623599364456832000, by norm_num, R7.Core.Certificates.Terminal118.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_13, 127486311406824548197340793304262377473537815754526310454128640000, by norm_num, R7.Core.Certificates.Terminal118.positive_13⟩
theorem bound_64 : ordinaryBindings polynomial_64 witness_64 := by
 decide +kernel
theorem positive_64 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_64 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_64 ρ hρ u
def polynomial_65 : BiPoly := [[300797752224],[-95463642750],[2913188558532],[-399940002000],[7212598394112],[-318358170000],[5073772375656],[0],[77789294352]]
def witness_65 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_14, 601595504448, by norm_num, R7.Core.Certificates.Terminal118.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_15, 3496008973757301401138172, by norm_num, R7.Core.Certificates.Terminal118.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_16, 50334391012590487734752979294654486528, by norm_num, R7.Core.Certificates.Terminal118.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_17, 510416158093068438919705304063802546628728014324736, by norm_num, R7.Core.Certificates.Terminal118.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_18, 79409825527837335612012177581829596176218657531310722437382144, by norm_num, R7.Core.Certificates.Terminal118.positive_18⟩
theorem bound_65 : ordinaryBindings polynomial_65 witness_65 := by
 decide +kernel
theorem positive_65 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_65 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_65 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8010
