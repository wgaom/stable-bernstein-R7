import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal039
import R7.Certificates.Spectral.Terminal.Terminal040

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry026
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_156 : BiPoly := [[61076027414223360,1099749684929841400,4919851993142702400],[0,2937716265621879000,13367115829819800000],[731139326668762560,35819515439391468400,114335849347727855400],[0,37694070694446816300,105114401118195345000],[3572223209957213280,362397095434526102250,659451031727694257700],[0,78595025371499925000,297169297465820625000],[8993967927280804800,1171630530457927888500,1565289946846239732000],[0,-3471039892461577500,342182343209598000000],[12117592903316582880,1481330214023384142000,1594110916462907779200],[0,-31740297139049191200,121791184169311800000],[8105415411150630360,683408926166020772400,538646097780927932400],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
def witness_156 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_0, 92000, by norm_num, R7.Core.Certificates.Terminal039.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_1, 3680000, by norm_num, R7.Core.Certificates.Terminal039.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal039.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_3, 34560000000, by norm_num, R7.Core.Certificates.Terminal039.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_4, 155520000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_5, 453496320000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_6, 18066564166717440000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_6⟩
theorem bound_156 : minorBindings polynomial_156 witness_156 := by
 decide +kernel
theorem positive_156 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_156 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_156 ρ hρ u
def polynomial_157 : BiPoly := [[254615646752801280,5924844631711057200,24341950817164915200],[0,12352491372761172000,49970109794688900000],[3018306546985729680,166808916786218177700,506419011932816221200],[0,140163037547769452700,385509211363484505000],[14596421747869639440,1542204397936658448000,2805902510772416799600],[0,277895883822410763000,1067400576324812925000],[36404973232371349200,4814774448028613491500,6479863008168761253000],[0,-14968097176531900500,1204670853381565350000],[48679801148408339520,5989661126682840828000,6459022940596769836800],[0,-110280156483119817600,423157690982426400000],[32421661644602521440,2733635704664083089600,2154584391123711729600],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
def witness_157 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_8, 22632000, by norm_num, R7.Core.Certificates.Terminal039.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_9, 198720000, by norm_num, R7.Core.Certificates.Terminal039.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_10, 11664000, by norm_num, R7.Core.Certificates.Terminal039.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_11, 9447840000000, by norm_num, R7.Core.Certificates.Terminal039.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_12, 127545840000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_13, 1487694677760000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_14, 237069454995666247680000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_14⟩
theorem bound_157 : minorBindings polynomial_157 witness_157 := by
 decide +kernel
theorem positive_157 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_157 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_157 ρ hρ u
def polynomial_158 : BiPoly := [[673620990669210240,19707728180301862600,76999417809517071600],[0,30854937566616316000,116672528805626700000],[7828847174100761280,492948592458447364200,1424516193567519752700],[0,310767754458101206800,869627906302215420000],[37105772749874831520,4116008678240039934000,7485583265954330086800],[0,576077571074380383000,2312787202529733675000],[90609077649075130800,12211508140108765708500,16578778668476000697000],[0,-42040013185861141500,2497763419834054050000],[118570625615999249280,14711480166394324152000,15906149403632202355200],[0,-219118742293257676800,840783908880115200000],[77277437253264074400,6515654994987868296000,5135478925079814696000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_158 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_16, 92000, by norm_num, R7.Core.Certificates.Terminal039.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_17, 3680000, by norm_num, R7.Core.Certificates.Terminal039.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_18, 48000, by norm_num, R7.Core.Certificates.Terminal039.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_19, 4320000000, by norm_num, R7.Core.Certificates.Terminal039.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_20, 408240000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_21, 351837561600000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_22, 130821998527219507200000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_22⟩
theorem bound_158 : minorBindings polynomial_158 witness_158 := by
 decide +kernel
theorem positive_158 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_158 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_158 ρ hρ u
def polynomial_159 : BiPoly := [[1236343382859834720,44593522432042504050,166945875334678324800],[0,48229352932495257000,187489391062028400000],[13989324487812308280,1000417470196203439200,2764108460829581732700],[0,441116634011796525600,1330785944449456140000],[64369262698921141920,7513155314773432846500,13655110861609078335300],[0,757113465177402255000,3338452192325738625000],[152228056387506598800,20934768861473495458500,28677941266925325942000],[0,-81918157197384018000,3374389990985041350000],[192428045479179790560,24091350958673204094000,26121056759877767990400],[0,-276781569212536012800,1062042832269619200000],[120796836127470684720,10184997544796825704800,8027564424993184024800],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_159 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_24, 207000, by norm_num, R7.Core.Certificates.Terminal039.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_25, 74520000, by norm_num, R7.Core.Certificates.Terminal039.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_26, 3888000, by norm_num, R7.Core.Certificates.Terminal039.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_27, 1049760000000, by norm_num, R7.Core.Certificates.Terminal039.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_28, 529079040000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_29, 64797368186880000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_30, 36139921361561565757440000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_30⟩
theorem bound_159 : minorBindings polynomial_159 witness_159 := by
 decide +kernel
theorem positive_159 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_159 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_159 ρ hρ u
def polynomial_160 : BiPoly := [[1633882882725627840,71169676703724374100,255437953176718155600],[0,46383493768919298000,215839261778412600000],[17823092303869143480,1432009184579980837200,3804646087921106338200],[0,402349624905238216200,1438980235200694530000],[78835341068548328880,9658947489293877459750,17541686815570435286700],[0,638267044369151394000,3349005999100749900000],[178523397732152005200,25031091206861121406500,34574197537551031668000],[0,-110380236706424412000,3107261568177934650000],[215151150042087658560,27163733201858684844000,29528795723331783110400],[0,-234615627027813729600,900247244541044400000],[128117856498832544400,10802270123269360596000,8514083481053376996000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_160 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_0, 414000, by norm_num, R7.Core.Certificates.Terminal040.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_1, 298080000, by norm_num, R7.Core.Certificates.Terminal040.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_2, 93312000, by norm_num, R7.Core.Certificates.Terminal040.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_3, 25194240000000, by norm_num, R7.Core.Certificates.Terminal040.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_4, 38093690880000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_5, 54429789276979200000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_6, 30357533943711715236249600000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_6⟩
theorem bound_160 : minorBindings polynomial_160 witness_160 := by
 decide +kernel
theorem positive_160 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_160 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_160 ρ hρ u
def polynomial_161 : BiPoly := [[1555356561764483520,79975943400954327300,275184746100840466800],[0,24220241740665018000,179311165242501600000],[16205525104430409120,1438665213046065759300,3700465401700332145800],[0,224913278698103786100,1110758837637866715000],[68110524977536535760,8704326305783724147000,15796063635225122093400],[0,335068681755164643000,2366793270087467175000],[145808697599714574000,20784360485677645732500,28905209239934883285000],[0,-100078600045483300500,1991544279837332850000],[165189640138610230080,20997941465235939372000,22873535628267671827200],[0,-137669999269777027200,528255679592440800000],[91919477995987793760,7750200151932938078400,6108517037200200638400],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_161 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_8, 2898000, by norm_num, R7.Core.Certificates.Terminal040.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_9, 49680000, by norm_num, R7.Core.Certificates.Terminal040.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_10, 432000, by norm_num, R7.Core.Certificates.Terminal040.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_11, 194400000000, by norm_num, R7.Core.Certificates.Terminal040.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_12, 55112400000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_13, 499979692800000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_14, 185904945275522457600000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_14⟩
theorem bound_161 : minorBindings polynomial_161 witness_161 := by
 decide +kernel
theorem positive_161 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_161 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_161 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry026
