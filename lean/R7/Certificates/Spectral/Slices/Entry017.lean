import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal025
import R7.Certificates.Spectral.Terminal.Terminal026

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry017
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_102 : BiPoly := [[1042704614126103840,42732487904322477850,171164259842470245600],[0,33952872573596574000,184245048502228800000],[10562108894052483780,865699160367810364200,2302445927861021027700],[0,270800718791973195300,1054844955484959195000],[42271986856255369920,5243847135756315820875,9519137457353676667800],[0,369606199629175110000,2078441610866490375000],[85459859370097570800,12042560915824509193500,16665579117035782047000],[0,-63849263568506923500,1629446967401110200000],[91390860545269451040,11562991901401601556000,12577919713208382153600],[0,-104754135570022310400,401953710824265600000],[48196717444798909560,4063711141610854700400,3202917119062937060400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_102 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal025.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_17, 8280000, by norm_num, R7.Core.Certificates.Terminal025.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_18, 144000, by norm_num, R7.Core.Certificates.Terminal025.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_19, 12960000000, by norm_num, R7.Core.Certificates.Terminal025.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_20, 1224720000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_21, 8332994880000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_22, 1549207877296020480000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_22⟩
theorem bound_102 : minorBindings polynomial_102 witness_102 := by
 decide +kernel
theorem positive_102 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_102 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_102 ρ hρ u
def polynomial_103 : BiPoly := [[864681875128964160,44008346148115200900,161083974140109374400],[0,18029703091217319000,139316697091860300000],[8329017702015280080,759637603545477983700,1947407513762361944700],[0,143043474289115027100,734419070172080865000],[31545134149958538480,4085474142485533277250,7410898484857333213200],[0,178575178176381636000,1317071097383306850000],[60074213254738200000,8605103349391819515000,11989404330087318750000],[0,-48781052611453674000,933635592843976800000],[60223557125435820480,7669279165250077272000,8358961160068004563200],[0,-54848331795837369600,210459380700254400000],[29632701503131336800,2498484246198355512000,1969243798338876312000],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
def witness_103 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal025.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_25, 16560000, by norm_num, R7.Core.Certificates.Terminal025.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_26, 1296000, by norm_num, R7.Core.Certificates.Terminal025.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_27, 5832000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_28, 209952000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_29, 69384936960000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_30, 7371158180020715520000000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_30⟩
theorem bound_103 : minorBindings polynomial_103 witness_103 := by
 decide +kernel
theorem positive_103 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_103 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_103 ρ hρ u
def polynomial_104 : BiPoly := [[511313430803814720,30671600011258389675,104880413390838274800],[0,4836223503498651000,75443838069728700000],[4613483913892164900,456201778105272778500,1138442008292702653500],[0,47705934705614052600,362643538469313690000],[16288849049736483360,2177762081117381552625,3948139198387173002400],[0,56072175924012084000,588431927052508275000],[28766966118554635200,4167951573337950339000,5834058301682023743000],[0,-24183549986101101000,376087751579653200000],[26631059688657737280,3405778201839947967000,3716812028515232275200],[0,-20156247088301311200,77341846881241800000],[12070968112304971020,1017764906171977171800,802177253146865791800],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
def witness_104 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_0, 34500, by norm_num, R7.Core.Certificates.Terminal026.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_1, 62100000, by norm_num, R7.Core.Certificates.Terminal026.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_2, 486000000, by norm_num, R7.Core.Certificates.Terminal026.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_3, 262440000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_4, 2361960000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_5, 1147912560000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_6, 45730990547003520000000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_6⟩
theorem bound_104 : minorBindings polynomial_104 witness_104 := by
 decide +kernel
theorem positive_104 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_104 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_104 ρ hρ u
def polynomial_105 : BiPoly := [[196761974681049120,13113008982819726300,43072946570540620800],[0,422339772981555000,26827673533303500000],[1633279362619295160,169390631618487977400,416327686751111414400],[0,10471846614970560300,116953339672796445000],[5260577281253980560,715521715468908169500,1296804043805864000400],[0,12033435274256826000,170904089709427725000],[8444717977523198400,1230526323191893068000,1726349583633584256000],[0,-7016846349211636500,98271728622688050000],[7105944127368331440,910565139146124816000,994316681894859489600],[0,-4782353502432211200,18350442455716800000],[2934218482172808840,247398930260817555600,194993748659045595600],[0,0,0],[448932439011941280,-1891153445141188800,2254563784377115200]]
def witness_105 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_8, 414000, by norm_num, R7.Core.Certificates.Terminal026.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_9, 298080000, by norm_num, R7.Core.Certificates.Terminal026.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_10, 93312000, by norm_num, R7.Core.Certificates.Terminal026.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_11, 33592320000000, by norm_num, R7.Core.Certificates.Terminal026.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_12, 340122240000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_13, 110199605760000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_14, 975594465002741760000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_14⟩
theorem bound_105 : minorBindings polynomial_105 witness_105 := by
 decide +kernel
theorem positive_105 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_105 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_105 ρ hρ u
def polynomial_106 : BiPoly := [[10311537095907840,89949596868231600,717955822185105600],[0,448352480901496000,2674889786905200000],[119412440172262080,5196211894623101200,17651690958055012200],[0,6579328460472968400,19271383999757460000],[545812896390269760,53812218201675094500,97890968806684403400],[0,12975323559803235000,49306977922834125000],[1270140508814464800,163983645187688398500,218066958279270882000],[0,-490280035061673000,51324076204574850000],[1577004399619320240,192150450835736661000,206561990128371681600],[0,-4316131241130506400,16561493819184600000],[973230882700882140,82058061027102852600,64676144357208192600],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_106 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_16, 552000, by norm_num, R7.Core.Certificates.Terminal026.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_17, 14720000, by norm_num, R7.Core.Certificates.Terminal026.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_18, 128000, by norm_num, R7.Core.Certificates.Terminal026.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_19, 34560000000, by norm_num, R7.Core.Certificates.Terminal026.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_20, 1866240000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_21, 302330880000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_22, 1338264012349440000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_22⟩
theorem bound_106 : minorBindings polynomial_106 witness_106 := by
 decide +kernel
theorem positive_106 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_106 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_106 ρ hρ u
def polynomial_107 : BiPoly := [[90424248379499520,1223096358017329800,7385264423863156800],[0,4274337044094708000,21414585963279600000],[1037002769917012800,50099151077813577000,162189600266352402000],[0,54035242187708998800,153666786421670220000],[4741240383569208960,482161638571730745750,877180161526737993900],[0,102811123295551413000,391717881786040425000],[11070819299801754000,1445205057518071147500,1932534353221792110000],[0,-4374009533396898000,407581235351351100000],[13834915091481048480,1693440101047301982000,1823118302845058083200],[0,-34520469151228682400,132459025118448600000],[8628345437676477480,727499824628344693200,573397458928084573200],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
def witness_107 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_24, 276000, by norm_num, R7.Core.Certificates.Terminal026.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_25, 993600000, by norm_num, R7.Core.Certificates.Terminal026.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_26, 432000000, by norm_num, R7.Core.Certificates.Terminal026.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_27, 583200000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_28, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_29, 6611976345600000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_30, 263410505550740275200000000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_30⟩
theorem bound_107 : minorBindings polynomial_107 witness_107 := by
 decide +kernel
theorem positive_107 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_107 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_107 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry017
