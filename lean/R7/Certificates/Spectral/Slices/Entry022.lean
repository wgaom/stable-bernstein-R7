import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal033
import R7.Certificates.Spectral.Terminal.Terminal034

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry022
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_132 : BiPoly := [[2160663619173304320,106554091719346698675,363279013137680338800],[0,69749513500693614000,110534357290051800000],[22489081029723015720,1918157871987775935800,4979039529548205739800],[0,378782810491432519800,659912648458841370000],[94175127395456955120,11793397187876177947125,21417094480963735585800],[0,460205486958396240000,1360418564690154000000],[201952340901499903200,28555836538998850434000,39593833692644346363000],[0,3643460232242796000,1095834766924522800000],[231717026271820491360,29360109503692878624000,31951370179604038262400],[0,-67033036293661065600,257213498440298400000],[132388451715460295880,11162345794045005949200,8797886263755156229200],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_132 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_0, 34500, by norm_num, R7.Core.Certificates.Terminal033.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_1, 135240000, by norm_num, R7.Core.Certificates.Terminal033.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_2, 32000, by norm_num, R7.Core.Certificates.Terminal033.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_3, 17280000000, by norm_num, R7.Core.Certificates.Terminal033.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_4, 243855360000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_5, 7347849707520000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_6, 4098171238073739509760000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_6⟩
theorem bound_132 : minorBindings polynomial_132 witness_132 := by
 decide +kernel
theorem positive_132 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_132 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_132 ρ hρ u
def polynomial_133 : BiPoly := [[3963695370029881920,220827692577267704550,731421161900056072800],[0,79641572485434967000,111588089635467900000],[39544896031608106800,3626087843679545462000,9203971766118332112000],[0,377388171309367259100,591041147981221665000],[157888599972595758000,20373964492661374593750,36975513709252699470000],[0,407081963289597156000,1050926335120148850000],[321620173704938397600,45981259960842172467000,64038525983647066134000],[0,17016286042679742000,720676378096365600000],[349085526356104614720,44415241345587468888000,48396287537894495404800],[0,-36039266824548960000,138286827118440000000],[187906189531621065120,15843329514128395540800,12487322438878286260800],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
def witness_133 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_8, 69000, by norm_num, R7.Core.Certificates.Terminal033.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_9, 901600000, by norm_num, R7.Core.Certificates.Terminal033.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_10, 8000000, by norm_num, R7.Core.Certificates.Terminal033.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_11, 12960000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_12, 3265920000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_13, 88885278720000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_14, 66099536097963540480000000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_14⟩
theorem bound_133 : minorBindings polynomial_133 witness_133 := by
 decide +kernel
theorem positive_133 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_133 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_133 ρ hρ u
def polynomial_134 : BiPoly := [[4515560903451257280,277963380119587006575,900870100110072205200],[0,36545685961906149000,49551197264106300000],[42344279771611356000,4121685413922297825000,10278691996544659665000],[0,146705996530159682400,201572095882876560000],[158528097172097790480,20954731025562218329125,38009409801360845893200],[0,135767944249168896000,267280125972996600000],[301409491959951474600,43454669811099560442000,60721393161769663689000],[0,12431818309348336500,129912427917965700000],[304167079658846738880,38816008419215478402000,42333524141139556819200],[0,-3243534014209406400,12445814440659600000],[151911172705758588360,12808406003305098992400,10095270413249004152400],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_134 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_16, 103500, by norm_num, R7.Core.Certificates.Terminal033.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_17, 10143000000, by norm_num, R7.Core.Certificates.Terminal033.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_18, 13500000000, by norm_num, R7.Core.Certificates.Terminal033.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_19, 7290000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_20, 2411167500000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_21, 161712181890000000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_22, 90192946106327692320000000000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_22⟩
theorem bound_134 : minorBindings polynomial_134 witness_134 := by
 decide +kernel
theorem positive_134 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_134 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_134 ρ hρ u
def polynomial_135 : BiPoly := [[3040455862123579584,201059440597143785160,642191422992053002560],[0,0,0],[26369932961444264784,2665069228584949137760,6574828309777286170560],[0,0,0],[90429791886271484640,12118437170004704193000,21975052830165736617600],[0,0,0],[156948173143236028800,22728226900195125666000,31814996751478601892000],[0,0,0],[144636225559773564960,18485565633478831104000,20169950222922379286400],[0,0,0],[66133217354635465776,5576028958868565183840,4394888806410409839840],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
def witness_135 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_24, 165600, by norm_num, R7.Core.Certificates.Terminal033.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_25, 259660800, by norm_num, R7.Core.Certificates.Terminal033.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_26, 401408, by norm_num, R7.Core.Certificates.Terminal033.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_27, 433520640000, by norm_num, R7.Core.Certificates.Terminal033.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_28, 436988805120000000, by norm_num, R7.Core.Certificates.Terminal033.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_29, 322302666375954432000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_30, 71904111808090755402458726400000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_30⟩
theorem bound_135 : minorBindings polynomial_135 witness_135 := by
 decide +kernel
theorem positive_135 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_135 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_135 ρ hρ u
def polynomial_136 : BiPoly := [[128259657569869056,6055982702167470940,20759907228414275040],[0,4834473290029329200,6983175974904540000],[1364444250599899872,113510253990586168580,296870299997329833480],[0,26213213551137775200,42355219377625380000],[5814536638784403600,721347969499618882500,1310347539486278199000],[0,31601275700346228600,88137345386755935000],[12706554306423625560,1791510925274597936700,2481219991108788710400],[0,603923651585704800,70074262358338140000],[14865308404379727840,1882129602438512406000,2047775470592300265600],[0,-3964319350700385600,15211550983028400000],[8663207439444867288,730439217859166287920,575714216337895015920],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_136 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_0, 64400, by norm_num, R7.Core.Certificates.Terminal034.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_1, 220800, by norm_num, R7.Core.Certificates.Terminal034.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_2, 128, by norm_num, R7.Core.Certificates.Terminal034.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_3, 2304000, by norm_num, R7.Core.Certificates.Terminal034.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_4, 3483648000000, by norm_num, R7.Core.Certificates.Terminal034.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_5, 4740548198400000000, by norm_num, R7.Core.Certificates.Terminal034.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_6, 176265429594569441280000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_6⟩
theorem bound_136 : minorBindings polynomial_136 witness_136 := by
 decide +kernel
theorem positive_136 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_136 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_136 ρ hρ u
def polynomial_137 : BiPoly := [[782883624127772160,40720421694741687150,136127981869414844400],[0,23300409235974866000,15672112159961700000],[8074480658490195120,709427340681736344300,1823238084611491885800],[0,107193106252303561200,85244882537568780000],[33490101747170134080,4249470813617630132250,7715514923652425879700],[0,114854046654800673000,150266441212430175000],[71024884128030477600,10098800584861140544500,14034444740604800334000],[0,15539162733234315000,85785065423835750000],[80395809950314031040,10211920467548965956000,11121585264935479353600],[0,-840916225906142400,3226692632763600000],[45146292290064801360,3806514233913965162400,3000200845704523322400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_137 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_8, 483000, by norm_num, R7.Core.Certificates.Terminal034.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal034.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal034.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal034.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_12, 4898880000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_13, 66663959040000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_14, 12393663018368163840000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_14⟩
theorem bound_137 : minorBindings polynomial_137 witness_137 := by
 decide +kernel
theorem positive_137 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_137 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_137 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry022
