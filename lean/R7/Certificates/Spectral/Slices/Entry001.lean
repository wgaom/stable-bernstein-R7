import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal001
import R7.Certificates.Spectral.Terminal.Terminal002

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry001
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_6 : BiPoly := [[80623330668629424,1671090749470944885,9451788755851388160],[0,3266670776965111200,15917511072475440000],[664388820090013428,42052531127402339670,123230835741782738520],[0,24746632070979985200,77377925899136880000],[2234166967687037040,252608005877816273625,459085695088555083600],[0,30920245884833911200,135135773035903395000],[3897386101821682080,530761487356404953100,723701111423766892200],[0,-2221260063508004400,97024610082308580000],[3679676932445080560,459143345731126959000,497308527955800590400],[0,-5766282691927833600,22125892338950400000],[1748910422047555368,147459560412883335120,116223996725490543120],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
def witness_6 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_16, 6900, by norm_num, R7.Core.Certificates.Terminal001.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_17, 82800, by norm_num, R7.Core.Certificates.Terminal001.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_18, 432, by norm_num, R7.Core.Certificates.Terminal001.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_19, 7776000, by norm_num, R7.Core.Certificates.Terminal001.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_20, 1959552000000, by norm_num, R7.Core.Certificates.Terminal001.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_21, 888852787200000000, by norm_num, R7.Core.Certificates.Terminal001.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_22, 5508294674830295040000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_22⟩
theorem bound_6 : minorBindings polynomial_6 witness_6 := by
 decide +kernel
theorem positive_6 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_6 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_6 ρ hρ u
def polynomial_7 : BiPoly := [[87539000980548384,2609812347148543410,12417718965374194560],[0,3193892914627135800,15878312121765960000],[699269822350858404,51277440128968947060,142254154881857983860],[0,21054427362804795300,72752032318561695000],[2272862658102765120,271412558348957575875,492935942597908173300],[0,23967183275563624200,118728303034458195000],[3820719963001349520,531206889278021793900,730907175455267176800],[0,-2518412392921741200,79096268300645340000],[3463964511248812320,435995172758307618000,473507500533838588800],[0,-4376196685838088000,16791971864382000000],[1574600413205606328,132762594258775361520,104640209676438329520],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
def witness_7 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_24, 41400, by norm_num, R7.Core.Certificates.Terminal001.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_25, 2980800, by norm_num, R7.Core.Certificates.Terminal001.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_26, 279936, by norm_num, R7.Core.Certificates.Terminal001.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_27, 15116544000, by norm_num, R7.Core.Certificates.Terminal001.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_28, 2176782336000000, by norm_num, R7.Core.Certificates.Terminal001.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_29, 141055495372800000000, by norm_num, R7.Core.Certificates.Terminal001.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_30, 749256549122105671680000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_30⟩
theorem bound_7 : minorBindings polynomial_7 witness_7 := by
 decide +kernel
theorem positive_7 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_7 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_7 ρ hρ u
def polynomial_8 : BiPoly := [[74287684318355280,2967945206856127200,12335614758405025200],[0,2128489721240049000,12365882225511300000],[569173111215814980,47408337806475033450,125642885926008710700],[0,12790492725271375800,52744418094555270000],[1768800375055780920,221794323235310343375,402523275260070532800],[0,13236796986446682000,79337962068571575000],[2832070053437658000,401059977039737392500,556142653149851970000],[0,-2076604255101636000,48397620761215200000],[2435665493701553040,308843512503326406000,336177226437766833600],[0,-2471264010826214400,9482525288121600000],[1045860053051694240,88181796924647841600,69502722294313281600],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
def witness_8 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_0, 1656000, by norm_num, R7.Core.Certificates.Terminal002.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_1, 894240000, by norm_num, R7.Core.Certificates.Terminal002.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_2, 1458000, by norm_num, R7.Core.Certificates.Terminal002.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_3, 1968300000000, by norm_num, R7.Core.Certificates.Terminal002.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_4, 3259504800000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_5, 1652994086400000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_6, 5487718865640422400000000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_6⟩
theorem bound_8 : minorBindings polynomial_8 witness_8 := by
 decide +kernel
theorem positive_8 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_8 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_8 ρ hρ u
def polynomial_9 : BiPoly := [[48186606044338560,2434460942013770025,9093751625603570400],[0,901693193191263000,7373247000758100000],[349988434846991820,32364752754557562300,82707893693442838800],[0,5347628113428279900,28932992677696185000],[1026454103659313280,133995184333032337875,243015508997172632700],[0,5073718478652288000,39693640693952925000],[1544765483693268000,221993077954141800000,309697843237021620000],[0,-1206209636977117500,22000945225401000000],[1244011438743527520,158625317001772503000,172957726567153756800],[0,-1032553597116045600,3962027348393400000],[498720303075576420,42049653163142257800,33142501834788277800],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
def witness_9 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_8, 310500, by norm_num, R7.Core.Certificates.Terminal002.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_9, 335340000, by norm_num, R7.Core.Certificates.Terminal002.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_10, 314928000, by norm_num, R7.Core.Certificates.Terminal002.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_11, 1700611200000000, by norm_num, R7.Core.Certificates.Terminal002.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_12, 51656065200000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_13, 2789427520800000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_14, 4115789149230316800000000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_14⟩
theorem bound_9 : minorBindings polynomial_9 witness_9 := by
 decide +kernel
theorem positive_9 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_9 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_9 ρ hρ u
def polynomial_10 : BiPoly := [[22888637871060816,1377691717037196465,4758378606016633440],[0,209809443365852400,3223159407731880000],[154843368144426684,15477093763338815010,38529686898153241560],[0,1489189403571015600,11508617912174640000],[421579364002932240,56646785413868131125,102683419307328464100],[0,1330535348357443200,14305749899722470000],[587010883803441840,85201488822744208800,119341546835134193100],[0,-467438581385596800,7180494058857510000],[436660580771086680,55878816058331089500,60993623815154071200],[0,-308908001353276800,1185315661015200000],[161720952647808276,13635518598533508840,10747180206620664840],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
def witness_10 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_16, 62100, by norm_num, R7.Core.Certificates.Terminal002.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_17, 154256400, by norm_num, R7.Core.Certificates.Terminal002.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_18, 7243344, by norm_num, R7.Core.Certificates.Terminal002.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_19, 1173421728000, by norm_num, R7.Core.Certificates.Terminal002.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_20, 63364773312000000, by norm_num, R7.Core.Certificates.Terminal002.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_21, 684339551769600000000, by norm_num, R7.Core.Certificates.Terminal002.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_22, 302922081383351316480000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_22⟩
theorem bound_10 : minorBindings polynomial_10 witness_10 := by
 decide +kernel
theorem positive_10 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_10 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_10 ρ hρ u
def polynomial_11 : BiPoly := [[7227990906650784,485890651982423160,1603433607761410560],[0,22932613210993200,941284521978840000],[44543982616889868,4653677678882717520,11420786745805893120],[0,285633165480219000,3024594972622350000],[109977225392069280,15001846489373976000,27186767208807235200],[0,245264831701426800,3379974177698280000],[139028893532394120,20277301439462288400,28457405799002290800],[0,-108510521756880600,1530715853917170000],[94243290813903600,12080141316603765000,13192452202429224000],[0,-60065444707581600,230478045197400000],[31956834954357324,2694443794919795160,2123694292326239160],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
def witness_11 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_24, 13413600, by norm_num, R7.Core.Certificates.Terminal002.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_25, 8692012800, by norm_num, R7.Core.Certificates.Terminal002.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_26, 1836660096, by norm_num, R7.Core.Certificates.Terminal002.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_27, 1785233613312000, by norm_num, R7.Core.Certificates.Terminal002.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_28, 723019613391360000000, by norm_num, R7.Core.Certificates.Terminal002.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_29, 23425835473880064000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_30, 1885348720274625758822400000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_30⟩
theorem bound_11 : minorBindings polynomial_11 witness_11 := by
 decide +kernel
theorem positive_11 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_11 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_11 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry001
