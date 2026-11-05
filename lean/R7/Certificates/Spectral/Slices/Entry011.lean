import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal016
import R7.Certificates.Spectral.Terminal.Terminal017

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry011
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_66 : BiPoly := [[1321231790009960640,73609230859089234850,243807053966685357600],[0,24347461246089070000,32253359436684000000],[11482186982967489960,1056948061757342684400,2679548008402673321400],[0,95745481455543385500,128551073847141825000],[40413914844538742640,5229265002151917156750,9489771362896442337600],[0,86124312530568216000,169049769394368600000],[73247630018455791000,10485708155183311380000,14611186141888248315000],[0,7506366154040155500,80916983614281150000],[71247927855311121600,9070423223173455780000,9885189891336397344000],[0,-1922094230642611200,7375297446316800000],[34571485086986559600,2914898287231414764000,2297451098062022364000],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
def witness_66 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal016.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal016.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_18, 576000, by norm_num, R7.Core.Certificates.Terminal016.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_19, 518400000000, by norm_num, R7.Core.Certificates.Terminal016.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_20, 1102248000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_21, 24998984640000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_22, 3098415754592040960000000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_22⟩
theorem bound_66 : minorBindings polynomial_66 witness_66 := by
 decide +kernel
theorem positive_66 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_66 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_66 ρ hρ u
def polynomial_67 : BiPoly := [[1505186967817085760,92654460039862335525,300290033370024068400],[0,11098607873420455000,12744862315258500000],[12266223925677473880,1196147608012635639450,2981330790959545886700],[0,35475634872980974200,23888193824722230000],[40413914844538742640,5348121770409204368625,9700640657068843587600],[0,25810895890234638000,-6622150752143325000],[68295798440172370800,9851267008591191103500,13768402645003577359500],[0,6306037398428607000,-27958822609633650000],[61777524276189519840,7885426591980464436000,8600580904446637545600],[0,2883141345963916800,-11062946169475200000],[27860549746571521560,2349065090298257780400,1851475296673512140400],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_67 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_24, 34500, by norm_num, R7.Core.Certificates.Terminal016.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_25, 230000, by norm_num, R7.Core.Certificates.Terminal016.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_26, 6000, by norm_num, R7.Core.Certificates.Terminal016.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_27, 540000000, by norm_num, R7.Core.Certificates.Terminal016.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_28, 476280000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_29, 154314720000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_30, 14344517382370560000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_30⟩
theorem bound_67 : minorBindings polynomial_67 witness_67 := by
 decide +kernel
theorem positive_67 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_67 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_67 ρ hρ u
def polynomial_68 : BiPoly := [[1013485287374526528,67019813532381261720,214063807664017667520],[0,19892812775637800,-1561041862249140000],[7606205821832214744,768727681396232364660,1896479205395523141960],[0,-1117072575598679100,-16474625698857165000],[22883409342690563520,3066707797723814844000,5561027905188839716800],[0,-1995718852519812000,-34288940874394575000],[35272145210996286000,5108058781024727632500,7150351273336107990000],[0,1853516762133340500,-24680544117654600000],[29173534245281714400,3728682562669824060000,4068466319673490896000],[0,1441570672981958400,-5531473084737600000],[12079683612747068472,1018499754479682570480,802756442499318402480],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_68 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_0, 55200, by norm_num, R7.Core.Certificates.Terminal017.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_1, 294400, by norm_num, R7.Core.Certificates.Terminal017.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_2, 384, by norm_num, R7.Core.Certificates.Terminal017.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_3, 518400000, by norm_num, R7.Core.Certificates.Terminal017.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_4, 81648000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_5, 999959385600000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_6, 37180989055104491520000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_6⟩
theorem bound_68 : minorBindings polynomial_68 witness_68 := by
 decide +kernel
theorem positive_68 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_68 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_68 ρ hρ u
def polynomial_69 : BiPoly := [[337828429124842176,22339937844127087240,71354602554672555840],[0,0,0],[2173201663380632784,219636480398923532760,541851201541578040560],[0,0,0],[5720852335672640880,766676949430953711000,1390256976297209929200],[0,0,0],[7838254491332508000,1135124173561050585000,1588966949630246220000],[0,0,0],[5834706849056342880,745736512533964812000,813693263934698179200],[0,0,0],[2196306111408557904,185181773541760467360,145955716818057891360],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
def witness_69 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_8, 18400, by norm_num, R7.Core.Certificates.Terminal017.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_9, 43276800, by norm_num, R7.Core.Certificates.Terminal017.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_10, 451584, by norm_num, R7.Core.Certificates.Terminal017.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_11, 406425600000, by norm_num, R7.Core.Certificates.Terminal017.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_12, 409677004800000000, by norm_num, R7.Core.Certificates.Terminal017.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_13, 10034792426373120000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_14, 62186443560964098883584000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_14⟩
theorem bound_69 : minorBindings polynomial_69 witness_69 := by
 decide +kernel
theorem positive_69 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_69 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_69 ρ hρ u
def polynomial_70 : BiPoly := [[36645616448534016,1730280772047848840,5931402065261221440],[0,1274153619500042800,1795084288524360000],[340220706736409856,28498032765540651840,74363724947015447040],[0,5825446500678300000,8856303392520000000],[1280352142527423840,159633996549998643000,289950236188289895600],[0,5940878687527053600,15118579898847810000],[2492221647025139040,352283789631173932800,488418664078039953600],[0,238584956885636400,9705374895184020000],[2613680598572259840,331322370836490216000,360614485503317145600],[0,-411877335137702400,1580420881353600000],[1371238736223332448,115616133745649392320,91125791452544080320],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
def witness_70 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_16, 18400, by norm_num, R7.Core.Certificates.Terminal017.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_17, 588800, by norm_num, R7.Core.Certificates.Terminal017.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_18, 294912, by norm_num, R7.Core.Certificates.Terminal017.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_19, 10616832000, by norm_num, R7.Core.Certificates.Terminal017.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_20, 1146617856000000, by norm_num, R7.Core.Certificates.Terminal017.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_21, 297203348275200000000, by norm_num, R7.Core.Certificates.Terminal017.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_22, 1578680465639992197120000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_22⟩
theorem bound_70 : minorBindings polynomial_70 witness_70 := by
 decide +kernel
theorem positive_70 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_70 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_70 ρ hρ u
def polynomial_71 : BiPoly := [[223681035465077760,11634406198497624900,38893709105547098400],[0,6127307435322563000,3780313034318100000],[2016394274838636000,178128961518153700000,457017802851346740000],[0,23552475120716060400,14316413494469760000],[7388840254119024960,941331948383503789500,1708967138046188621400],[0,21051302409411570000,15200337953800125000],[13954381536029187600,1988096701514086692000,2765086695606008484000],[0,3538678089677499000,857049480864450000],[14149059394194060480,1798831022956828452000,1959602068348494163200],[0,892400892798355200,-3424245242932800000],[7146710362519910640,602575612318426917600,474935269011140757600],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_71 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal017.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_25, 4508000000, by norm_num, R7.Core.Certificates.Terminal017.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_26, 40000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_27, 32400000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_28, 1749600000000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_29, 3401222400000000000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_30, 90332820833587200000000000000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_30⟩
theorem bound_71 : minorBindings polynomial_71 witness_71 := by
 decide +kernel
theorem positive_71 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_71 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_71 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry011
