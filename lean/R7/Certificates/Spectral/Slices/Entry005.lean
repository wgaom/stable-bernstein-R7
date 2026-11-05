import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal007
import R7.Certificates.Spectral.Terminal.Terminal008

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry005
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_30 : BiPoly := [[928127573087343264,29242889922407080860,130605245633298533760],[0,35234593964156248200,163487871668972340000],[8281174165130472444,603405256587171837660,1672227395086797647460],[0,256097849093337849300,848941296115664295000],[30105247143436446240,3570449371141668348000,6485987650542633786600],[0,330984755864803447200,1576029701454015870000],[56674012784520017880,7851758614483720949100,10788154553354352289200],[0,-34965057121485365700,1198527897427322490000],[57614065117566400800,7238649554545728060000,7857103508332756272000],[0,-75682460331552816000,290402336948724000000],[29406098491636803048,2479378190198015146320,1954184875175108434320],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
def witness_30 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_16, 82800, by norm_num, R7.Core.Certificates.Terminal007.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_17, 292118400, by norm_num, R7.Core.Certificates.Terminal007.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_18, 31104, by norm_num, R7.Core.Certificates.Terminal007.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_19, 38631168000, by norm_num, R7.Core.Certificates.Terminal007.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_20, 793618560000000, by norm_num, R7.Core.Certificates.Terminal007.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_21, 1079956136448000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_22, 120466404538538552524800000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_22⟩
theorem bound_30 : minorBindings polynomial_30 witness_30 := by
 decide +kernel
theorem positive_30 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_30 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_30 ρ hρ u
def polynomial_31 : BiPoly := [[1042704614126103840,42732487904322477850,171164259842470245600],[0,30646069184327712000,166933294569824400000],[8932364768148814800,737277550493224662000,1955196999877958082000],[0,204398487730460610600,806631558448686390000],[31087914018467435640,3871974097317080232375,7028470639187517207600],[0,240558222413553138000,1379363785249862925000],[55826108174581713000,7880971989813367770000,10914948458695289857500],[0,-38756778474440754000,959049876258926550000],[53919728117661379680,6827271627113851032000,7428263355697626691200],[0,-55740732688635724800,213883625943187200000],[26030294653731056640,2194746945680124057600,1729845532658463897600],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_31 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal007.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_25, 165600000, by norm_num, R7.Core.Certificates.Terminal007.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_26, 144000000, by norm_num, R7.Core.Certificates.Terminal007.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_27, 64800000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_28, 97977600000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_29, 28443289190400000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_30, 2643981443918541619200000000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_30⟩
theorem bound_31 : minorBindings polynomial_31 witness_31 := by
 decide +kernel
theorem positive_31 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_31 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_31 ρ hρ u
def polynomial_32 : BiPoly := [[864681875128964160,44008346148115200900,161083974140109374400],[0,16132934374693983000,126125872794197100000],[7035121064096098200,644058682529982445500,1648452861256245025500],[0,107121763548456605400,560677122451911510000],[23150205945030583440,3003994860656162598000,5449048524074393634600],[0,115670522721826296000,873363193556399100000],[39142640950694418600,5611000282880709357000,7820279883250291899000],[0,-29320115699911180500,550308381725048850000],[35443854527433433920,4514838610300587108000,4921237242215861932800],[0,-29311937017299820800,112473286056331200000],[15978417477178662000,1347221897459897580000,1061847146163119580000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_32 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_0, 138000, by norm_num, R7.Core.Certificates.Terminal008.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_1, 82800000, by norm_num, R7.Core.Certificates.Terminal008.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_2, 162000000, by norm_num, R7.Core.Certificates.Terminal008.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_3, 29160000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_4, 65610000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_5, 1062882000000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_6, 56458013020992000000000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_6⟩
theorem bound_32 : minorBindings polynomial_32 witness_32 := by
 decide +kernel
theorem positive_32 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_32 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_32 ρ hρ u
def polynomial_33 : BiPoly := [[511313430803814720,30671600011258389675,104880413390838274800],[0,4265008730013615000,68163774402325500000],[3885225150473171820,384551024451129016050,959138449497298851300],[0,35498992425417955200,275988552090217380000],[11898924802836384600,1590982474552119886875,2884389377205673989000],[0,36271732072260186000,389451518885083725000],[18648752200363729800,2701731665441749221000,3781666265582993044500],[0,-14413407241027950000,221841597464583750000],[15606688958782436160,1995753627890999379000,2177968443861111494400],[0,-10811780047364688000,41486048135532000000],[6493047829362601740,547461989240522016600,431496067577194956600],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
def witness_33 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_8, 34500, by norm_num, R7.Core.Certificates.Terminal008.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_9, 6210000, by norm_num, R7.Core.Certificates.Terminal008.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_10, 486000, by norm_num, R7.Core.Certificates.Terminal008.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_11, 43740000000, by norm_num, R7.Core.Certificates.Terminal008.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_12, 42515280000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_13, 20662426080000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_14, 411578914923031680000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_14⟩
theorem bound_33 : minorBindings polynomial_33 witness_33 := by
 decide +kernel
theorem positive_33 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_33 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_33 ρ hρ u
def polynomial_34 : BiPoly := [[196761974681049120,13113008982819726300,43072946570540620800],[0,357658043412087000,24172768471311900000],[1368136608947331660,141690169244186087400,348346813264171574400],[0,7786894859456501700,88522146930146355000],[3812543813591735040,517997403358817485500,938844942223235403600],[0,7801414648820442000,112582966643261325000],[5432425284321325800,791184792003543486000,1109772457988534622000],[0,-4151787836157157500,57855459146454000000],[4140421909757498160,530443359050326344000,579194185925086574400],[0,-2568512826067060800,9855680218441200000],[1573632024267595500,132680944446808095000,104575855303943595000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_34 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_16, 414000, by norm_num, R7.Core.Certificates.Terminal008.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_17, 149040000, by norm_num, R7.Core.Certificates.Terminal008.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_18, 11664000, by norm_num, R7.Core.Certificates.Terminal008.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_19, 2099520000000, by norm_num, R7.Core.Certificates.Terminal008.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_20, 14171760000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_21, 19131876000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_22, 84687019531488000000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_22⟩
theorem bound_34 : minorBindings polynomial_34 witness_34 := by
 decide +kernel
theorem positive_34 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_34 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_34 ρ hρ u
def polynomial_35 : BiPoly := [[39352394936209824,2622601796563945260,8614589314108124160],[0,67380798059269200,4491590815220040000],[236153812603828824,24464509053509605860,60142548997628084160],[0,1268293526803823400,14363307520975710000],[577380433308363720,78464464315954276500,142212005796416734800],[0,1123546601858896800,16159811612829030000],[731188995614813520,106502087040241293900,149393084423192686800],[0,-532342557121375800,7425761565976560000],[500536588989399120,64128137645317878000,70022777900868100800],[0,-297466964266118400,1141415080977600000],[172373230965927384,14533666530173440560,11455078304062744560],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
def witness_35 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_24, 82800, by norm_num, R7.Core.Certificates.Terminal008.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_25, 5961600, by norm_num, R7.Core.Certificates.Terminal008.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_26, 93312, by norm_num, R7.Core.Certificates.Terminal008.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_27, 5038848000, by norm_num, R7.Core.Certificates.Terminal008.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_28, 90699264000000, by norm_num, R7.Core.Certificates.Terminal008.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_29, 1959104102400000000, by norm_num, R7.Core.Certificates.Terminal008.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_30, 867195080002437120000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_30⟩
theorem bound_35 : minorBindings polynomial_35 witness_35 := by
 decide +kernel
theorem positive_35 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_35 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_35 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry005
