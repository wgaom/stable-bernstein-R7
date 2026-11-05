import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal031
import R7.Certificates.Spectral.Terminal.Terminal032

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry021
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_126 : BiPoly := [[3555001563209380800,166899157405262898250,585130239463286022000],[0,116796685446382970000,304476301420951500000],[37104273350894329200,3098052117918206663000,8109903021349579128000],[0,730290695027247267000,1843608696289613550000],[155546492394801690000,19312114491444797100000,35073032187122730225000],[0,960245642185296390000,3894286819454159625000],[333840985087045140000,47032682374350714825000,65109169432351441350000],[0,-71941497241593262500,3289079186446252500000],[383507364752045049600,48510584104168436040000,52764652436375988864000],[0,-224644763206355184000,861987889038276000000],[219630611140855790400,18518177354176046736000,14595571681805789136000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
def witness_126 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_16, 115000, by norm_num, R7.Core.Certificates.Terminal031.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_17, 138000000, by norm_num, R7.Core.Certificates.Terminal031.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_18, 16000000, by norm_num, R7.Core.Certificates.Terminal031.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_19, 216000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_20, 51030000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_21, 124994923200000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_22, 116190590797201536000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_22⟩
theorem bound_126 : minorBindings polynomial_126 witness_126 := by
 decide +kernel
theorem positive_126 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_126 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_126 ρ hρ u
def polynomial_127 : BiPoly := [[4985727335266593600,270722156214576417125,912470401309473174000],[0,100108507909391120000,328413326158606500000],[49734233854201785600,4517654536009407821500,11513703864389889204000],[0,583950487341289512000,1821305594655285300000],[198315413380606410000,25499315234236127945625,46277175889210995337500],[0,700348654138252680000,3478943632809078000000],[403226701396267761000,57562596634164203970000,80115473420659004490000],[0,-91937599406642430000,2651787525852801000000],[436870010306228688000,55547048312029861650000,60513528067006633920000],[0,-166381281840001032000,638424185196798000000],[234882736914526331400,19804161892660494426000,15609153048597857826000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
def witness_127 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal031.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_25, 34500000, by norm_num, R7.Core.Certificates.Terminal031.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_26, 8000000, by norm_num, R7.Core.Certificates.Terminal031.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_27, 21600000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_28, 136080000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_29, 4629441600000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_30, 4303355214711168000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_30⟩
theorem bound_127 : minorBindings polynomial_127 witness_127 := by
 decide +kernel
theorem positive_127 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_127 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_127 ρ hρ u
def polynomial_128 : BiPoly := [[4603208968766473920,280837397417840078300,917527210432880602800],[0,35697348509617965000,232542502848783000000],[43126221759230598480,4189700179860887749700,10461008972386039475700],[0,225715903179105375300,1166308989058663695000],[160998511512849272640,21272726601370996525500,38585037882520524725100],[0,256211709520879467000,2016044644134401325000],[305005362724770804000,43967575378974815797500,61433112405789607860000],[0,-78408207550540917000,1398160765140775650000],[306600650857196871840,39124922670509968026000,42669890019289641225600],[0,-82169528359971628800,315293965830043200000],[152521257736705410000,12859845384844476900000,10135813667920686900000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_128 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal032.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_1, 1840000, by norm_num, R7.Core.Certificates.Terminal032.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal032.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_3, 21600000000, by norm_num, R7.Core.Certificates.Terminal032.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_4, 2721600000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_5, 925888320000000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_6, 516402625765340160000000000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_6⟩
theorem bound_128 : minorBindings polynomial_128 witness_128 := by
 decide +kernel
theorem positive_128 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_128 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_128 ρ hρ u
def polynomial_129 : BiPoly := [[2608918034659836480,172548534932009511450,552539049909091333200],[0,-996728248615510000,104688573392425500000],[22571308017034617240,2285470036974671733600,5637242151957466889100],[0,34724309681878168800,494563570499655720000],[77130694074971255040,10348882876293898589250,18765337416612613766100],[0,47562168829832307000,798746367354684075000],[133278933120869178000,19311397931006351302500,27037461553543994895000],[0,-38524050707655807000,515877440460467400000],[122177002211144627040,15619252794725793906000,17043825719429181993600],[0,-28711282570224004800,110168505604357200000],[55517737816160769240,4680983720083389591600,3689436175123130031600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_129 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_8, 483000, by norm_num, R7.Core.Certificates.Terminal032.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal032.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal032.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_11, 21600000000, by norm_num, R7.Core.Certificates.Terminal032.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_12, 24494400000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_13, 166659897600000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_14, 30984157545920409600000000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_14⟩
theorem bound_129 : minorBindings polynomial_129 witness_129 := by
 decide +kernel
theorem positive_129 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_129 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_129 ρ hρ u
def polynomial_130 : BiPoly := [[100259868378673152,3827401363467021480,14106871444806103680],[0,4793309341658749000,11103754882213800000],[1094195043894254112,80812102016644627180,220273776832937365080],[0,32914073566595065500,73524207655646325000],[4830851456110895040,570930760884156370500,1037925072563689803600],[0,47400513266820868200,170909661556768095000],[10959252903757240200,1515543526417554076500,2081927636270162568000],[0,-2303147608989532200,159764286894381540000],[13369981523465790720,1678802349598171938000,1821898233911655244800],[0,-11892958052101156800,45634652949085200000],[8175139414687409976,689287712627663961840,543279612600548817840],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_130 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal032.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_17, 294400, by norm_num, R7.Core.Certificates.Terminal032.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_18, 128, by norm_num, R7.Core.Certificates.Terminal032.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_19, 34560000, by norm_num, R7.Core.Certificates.Terminal032.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_20, 13063680000000, by norm_num, R7.Core.Certificates.Terminal032.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_21, 17777055744000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_22, 660995360979635404800000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_22⟩
theorem bound_130 : minorBindings polynomial_130 witness_130 := by
 decide +kernel
theorem positive_130 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_130 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_130 ρ hρ u
def polynomial_131 : BiPoly := [[685558577845626624,29650152196903477260,104600336019661136160],[0,28883347895064234600,54260792571355020000],[7375917883482461952,582967068021692387280,1551432230490801595680],[0,177381861353198522100,347638281099815115000],[31936164284685895920,3876836191151325759000,7044817836149904007800],[0,237005366901501290400,777141020830572090000],[70997421630542597280,9921163355076456039600,13689442882136853835200],[0,-5097671872211482200,689515647758159040000],[84705869783536555680,10682795856110053032000,11609021113511866531200],[0,-47571832208404627200,182538611796340800000],[50515040562396831792,4259180791460490749280,3356981486815331501280],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
def witness_131 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_24, 27600, by norm_num, R7.Core.Certificates.Terminal032.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_25, 584236800, by norm_num, R7.Core.Certificates.Terminal032.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_26, 746496, by norm_num, R7.Core.Certificates.Terminal032.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_27, 3708592128000, by norm_num, R7.Core.Certificates.Terminal032.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_28, 137137287168000000, by norm_num, R7.Core.Certificates.Terminal032.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_29, 77259198036580761600000000, by norm_num, R7.Core.Certificates.Terminal032.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_30, 17236140415126834433564344320000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_30⟩
theorem bound_131 : minorBindings polynomial_131 witness_131 := by
 decide +kernel
theorem positive_131 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_131 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_131 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry021
