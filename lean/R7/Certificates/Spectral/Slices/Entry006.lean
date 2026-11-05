import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal009
import R7.Certificates.Spectral.Terminal.Terminal010

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry006
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_36 : BiPoly := [[6874358063938560,59966397912154400,478637214790070400],[0,278417117822888000,1615272178845600000],[67038562903726080,2988361764095491200,10038919614412147200],[0,3383819542429903200,9807699448081080000],[266117730578340480,26569091732503971000,48335814890447893200],[0,5699735928033516000,21705526563967350000],[549249949757606400,71318550774387888000,95115026212736976000],[0,-205808882199930000,19996112729938500000],[615722833317503520,75223374924490398000,80934498811817596800],[0,-1521657932592067200,5838777145000800000],[348620017683898080,29393932308215947200,23167574098104427200],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
def witness_36 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal009.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_1, 235520000, by norm_num, R7.Core.Certificates.Terminal009.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_2, 393216000, by norm_num, R7.Core.Certificates.Terminal009.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_3, 35389440000000, by norm_num, R7.Core.Certificates.Terminal009.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_4, 7644119040000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_5, 29720334827520000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_6, 43852235156666449920000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_6⟩
theorem bound_36 : minorBindings polynomial_36 witness_36 := by
 decide +kernel
theorem positive_36 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_36 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_36 ρ hρ u
def polynomial_37 : BiPoly := [[60282832252999680,815397572011553200,4923509615908771200],[0,2648895862150700000,12964791515490000000],[586587425407603200,28983733790820498000,92900857490282538000],[0,27940567184504917200,78613305453720180000],[2335318860177273600,240385747710307612500,437340651628237749000],[0,45439969708111230000,173384061960342375000],[4840265182238906400,635502747970003968000,852222318922652976000],[0,-1832541844374621000,159074614793448450000],[5453545095097888320,669435790768904268000,721353722828144428800],[0,-12098896719670008000,46424863389762000000],[3108528491014757880,262095896414925529200,206577535708097809200],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_37 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_8, 184000, by norm_num, R7.Core.Certificates.Terminal009.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_9, 3385600000, by norm_num, R7.Core.Certificates.Terminal009.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_10, 26496000000, by norm_num, R7.Core.Certificates.Terminal009.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_11, 9538560000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_12, 128770560000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_13, 41721661440000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_14, 554041301112668160000000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_14⟩
theorem bound_37 : minorBindings polynomial_37 witness_37 := by
 decide +kernel
theorem positive_37 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_37 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_37 ρ hρ u
def polynomial_38 : BiPoly := [[256202037075248640,4948992873327868600,25273595867226777600],[0,11755127329837168000,49846885296906600000],[2467857096893416320,138951307793899849800,421942702032125668800],[0,106223327658098463000,294991287990273450000],[9722801370772939680,1044623477827346211000,1900118126283555571200],[0,163001579035427532000,634010989014940950000],[19944638800573082400,2660199241786164108000,3594192419838237066000],[0,-8002289208060513000,565761838195281600000],[22241416632081249600,2748787416424432620000,2968347905837424864000],[0,-41908518850261219200,160807824677728800000],[12550320636620330880,1058181563095774099200,834032667531759379200],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_38 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_16, 1748000, by norm_num, R7.Core.Certificates.Terminal009.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_17, 7360000, by norm_num, R7.Core.Certificates.Terminal009.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_18, 1152000, by norm_num, R7.Core.Certificates.Terminal009.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_19, 414720000000, by norm_num, R7.Core.Certificates.Terminal009.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_20, 83980800000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_21, 11754624614400000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_22, 624380457601754726400000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_22⟩
theorem bound_38 : minorBindings polynomial_38 witness_38 := by
 decide +kernel
theorem positive_38 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_38 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_38 ρ hρ u
def polynomial_39 : BiPoly := [[687964603168005120,17966772019989658800,81765613053081160800],[0,30491203187374317000,119769672025737900000],[6491218348662351840,418571937063467247600,1206843152745552690600],[0,239522741381205667200,680163801799770180000],[25042221544831182720,2825138837170234569000,5136434700677845444800],[0,341222955441730956000,1395672900067328850000],[50239206341891060400,6825678084474752448000,9300083452807038336000],[0,-22350227798949151500,1184214261737011050000],[54711371760498169920,6816073267098902268000,7379029001866608172800],[0,-83370837254123260800,319903526733991200000],[30097528193376534240,2537676155942643441600,2000133897136348881600],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
def witness_39 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_24, 552000, by norm_num, R7.Core.Certificates.Terminal009.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_25, 99360000, by norm_num, R7.Core.Certificates.Terminal009.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_26, 3456000, by norm_num, R7.Core.Certificates.Terminal009.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_27, 3732480000000, by norm_num, R7.Core.Certificates.Terminal009.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_28, 88179840000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_29, 799967508480000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_30, 99149304146945310720000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_30⟩
theorem bound_39 : minorBindings polynomial_39 witness_39 := by
 decide +kernel
theorem positive_39 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_39 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_39 ρ hρ u
def polynomial_40 : BiPoly := [[1278134852916807360,43432341661086843900,179910835614742262400],[0,49428110449290114000,198264463611301800000],[11717083822516873920,860009421110813293800,2366660357931281977800],[0,345556600168431694800,1063059666378742620000],[43813704627029378160,5194517260829946004500,9438080824038599159400],[0,452097882351034110000,2044086534020302875000],[84996429724989590400,11770743496685473368000,16172623802017163286000],[0,-42755820286951075500,1614592219486094100000],[89250490696118129280,11210502262747308192000,12167311276246285555200],[0,-105955444464173942400,406563271728213600000],[47179909059887540160,3977978839045224854400,3135345027943465814400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_40 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_0, 138000, by norm_num, R7.Core.Certificates.Terminal010.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_1, 33120000, by norm_num, R7.Core.Certificates.Terminal010.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_2, 3456000, by norm_num, R7.Core.Certificates.Terminal010.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_3, 1244160000000, by norm_num, R7.Core.Certificates.Terminal010.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_4, 9797760000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_5, 177770557440000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_6, 33049768048981770240000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_6⟩
theorem bound_40 : minorBindings polynomial_40 witness_40 := by
 decide +kernel
theorem positive_40 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_40 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_40 ρ hρ u
def polynomial_41 : BiPoly := [[1705567895421217920,72806876653506075800,277962874661041312800],[0,50107029609616551000,235119665623808700000],[15030517167910803960,1239717105015116834400,3276949132772683331400],[0,322591661702940846900,1173129906861129735000],[53894950287969062160,6692975028617223184500,12151604684369940719400],[0,385680871512836190000,2078634975988458375000],[99911998673094589200,14085110822061766059000,19498883257432086228000],[0,-56308207722561144000,1502246783457337050000],[99864379537115094720,12636611768770640028000,13746284309861082604800],[0,-90818952397863379200,348482804338468800000],[50026972537639374480,4218029286228988423200,3324546883077985303200],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_41 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_8, 92000, by norm_num, R7.Core.Certificates.Terminal010.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_9, 11040000, by norm_num, R7.Core.Certificates.Terminal010.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_10, 3456000, by norm_num, R7.Core.Certificates.Terminal010.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_11, 622080000000, by norm_num, R7.Core.Certificates.Terminal010.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_12, 3605575680000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_13, 2133246689280000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_14, 396597216587781242880000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_14⟩
theorem bound_41 : minorBindings polynomial_41 witness_41 := by
 decide +kernel
theorem positive_41 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_41 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_41 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry006
