import R7.Spectral.SliceInteger
import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch04
import R7.Certificates.Spectral.Terminal.Batches.Batch05
import R7.Certificates.Spectral.Terminal.Batches.Batch06
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.Entry026
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_156 : BiPoly := r7_rat_grid%[[61076027414223360,1099749684929841400,4919851993142702400],[0,2937716265621879000,13367115829819800000],[731139326668762560,35819515439391468400,114335849347727855400],[0,37694070694446816300,105114401118195345000],[3572223209957213280,362397095434526102250,659451031727694257700],[0,78595025371499925000,297169297465820625000],[8993967927280804800,1171630530457927888500,1565289946846239732000],[0,-3471039892461577500,342182343209598000000],[12117592903316582880,1481330214023384142000,1594110916462907779200],[0,-31740297139049191200,121791184169311800000],[8105415411150630360,683408926166020772400,538646097780927932400],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
noncomputable def witness_156 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_0, 92000, by norm_num, R7.Core.Certificates.Terminal039.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_1, 3680000, by norm_num, R7.Core.Certificates.Terminal039.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal039.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_3, 34560000000, by norm_num, R7.Core.Certificates.Terminal039.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_4, 155520000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_5, 453496320000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_6, 18066564166717440000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_6⟩
theorem bound_156 : minorBindings polynomial_156 witness_156 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_156 witness_156 (by decide +kernel)
theorem positive_156 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_156 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_156 ρ hρ u
noncomputable def polynomial_157 : BiPoly := r7_rat_grid%[[254615646752801280,5924844631711057200,24341950817164915200],[0,12352491372761172000,49970109794688900000],[3018306546985729680,166808916786218177700,506419011932816221200],[0,140163037547769452700,385509211363484505000],[14596421747869639440,1542204397936658448000,2805902510772416799600],[0,277895883822410763000,1067400576324812925000],[36404973232371349200,4814774448028613491500,6479863008168761253000],[0,-14968097176531900500,1204670853381565350000],[48679801148408339520,5989661126682840828000,6459022940596769836800],[0,-110280156483119817600,423157690982426400000],[32421661644602521440,2733635704664083089600,2154584391123711729600],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
noncomputable def witness_157 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_8, 22632000, by norm_num, R7.Core.Certificates.Terminal039.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_9, 198720000, by norm_num, R7.Core.Certificates.Terminal039.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_10, 11664000, by norm_num, R7.Core.Certificates.Terminal039.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_11, 9447840000000, by norm_num, R7.Core.Certificates.Terminal039.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_12, 127545840000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_13, 1487694677760000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_14, 237069454995666247680000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_14⟩
theorem bound_157 : minorBindings polynomial_157 witness_157 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_157 witness_157 (by decide +kernel)
theorem positive_157 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_157 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_157 ρ hρ u
noncomputable def polynomial_158 : BiPoly := r7_rat_grid%[[673620990669210240,19707728180301862600,76999417809517071600],[0,30854937566616316000,116672528805626700000],[7828847174100761280,492948592458447364200,1424516193567519752700],[0,310767754458101206800,869627906302215420000],[37105772749874831520,4116008678240039934000,7485583265954330086800],[0,576077571074380383000,2312787202529733675000],[90609077649075130800,12211508140108765708500,16578778668476000697000],[0,-42040013185861141500,2497763419834054050000],[118570625615999249280,14711480166394324152000,15906149403632202355200],[0,-219118742293257676800,840783908880115200000],[77277437253264074400,6515654994987868296000,5135478925079814696000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_158 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_16, 92000, by norm_num, R7.Core.Certificates.Terminal039.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_17, 3680000, by norm_num, R7.Core.Certificates.Terminal039.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_18, 48000, by norm_num, R7.Core.Certificates.Terminal039.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_19, 4320000000, by norm_num, R7.Core.Certificates.Terminal039.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_20, 408240000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_21, 351837561600000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_22, 130821998527219507200000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_22⟩
theorem bound_158 : minorBindings polynomial_158 witness_158 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_158 witness_158 (by decide +kernel)
theorem positive_158 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_158 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_158 ρ hρ u
noncomputable def polynomial_159 : BiPoly := r7_rat_grid%[[1236343382859834720,44593522432042504050,166945875334678324800],[0,48229352932495257000,187489391062028400000],[13989324487812308280,1000417470196203439200,2764108460829581732700],[0,441116634011796525600,1330785944449456140000],[64369262698921141920,7513155314773432846500,13655110861609078335300],[0,757113465177402255000,3338452192325738625000],[152228056387506598800,20934768861473495458500,28677941266925325942000],[0,-81918157197384018000,3374389990985041350000],[192428045479179790560,24091350958673204094000,26121056759877767990400],[0,-276781569212536012800,1062042832269619200000],[120796836127470684720,10184997544796825704800,8027564424993184024800],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_159 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal039.polynomial_24, 207000, by norm_num, R7.Core.Certificates.Terminal039.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal039.polynomial_25, 74520000, by norm_num, R7.Core.Certificates.Terminal039.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal039.polynomial_26, 3888000, by norm_num, R7.Core.Certificates.Terminal039.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal039.polynomial_27, 1049760000000, by norm_num, R7.Core.Certificates.Terminal039.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal039.polynomial_28, 529079040000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal039.polynomial_29, 64797368186880000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal039.polynomial_30, 36139921361561565757440000000000000000, by norm_num, R7.Core.Certificates.Terminal039.positive_30⟩
theorem bound_159 : minorBindings polynomial_159 witness_159 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_159 witness_159 (by decide +kernel)
theorem positive_159 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_159 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_159 ρ hρ u
noncomputable def polynomial_160 : BiPoly := r7_rat_grid%[[1633882882725627840,71169676703724374100,255437953176718155600],[0,46383493768919298000,215839261778412600000],[17823092303869143480,1432009184579980837200,3804646087921106338200],[0,402349624905238216200,1438980235200694530000],[78835341068548328880,9658947489293877459750,17541686815570435286700],[0,638267044369151394000,3349005999100749900000],[178523397732152005200,25031091206861121406500,34574197537551031668000],[0,-110380236706424412000,3107261568177934650000],[215151150042087658560,27163733201858684844000,29528795723331783110400],[0,-234615627027813729600,900247244541044400000],[128117856498832544400,10802270123269360596000,8514083481053376996000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_160 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_0, 414000, by norm_num, R7.Core.Certificates.Terminal040.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_1, 298080000, by norm_num, R7.Core.Certificates.Terminal040.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_2, 93312000, by norm_num, R7.Core.Certificates.Terminal040.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_3, 25194240000000, by norm_num, R7.Core.Certificates.Terminal040.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_4, 38093690880000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_5, 54429789276979200000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_6, 30357533943711715236249600000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_6⟩
theorem bound_160 : minorBindings polynomial_160 witness_160 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_160 witness_160 (by decide +kernel)
theorem positive_160 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_160 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_160 ρ hρ u
noncomputable def polynomial_161 : BiPoly := r7_rat_grid%[[1555356561764483520,79975943400954327300,275184746100840466800],[0,24220241740665018000,179311165242501600000],[16205525104430409120,1438665213046065759300,3700465401700332145800],[0,224913278698103786100,1110758837637866715000],[68110524977536535760,8704326305783724147000,15796063635225122093400],[0,335068681755164643000,2366793270087467175000],[145808697599714574000,20784360485677645732500,28905209239934883285000],[0,-100078600045483300500,1991544279837332850000],[165189640138610230080,20997941465235939372000,22873535628267671827200],[0,-137669999269777027200,528255679592440800000],[91919477995987793760,7750200151932938078400,6108517037200200638400],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_161 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_8, 2898000, by norm_num, R7.Core.Certificates.Terminal040.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_9, 49680000, by norm_num, R7.Core.Certificates.Terminal040.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_10, 432000, by norm_num, R7.Core.Certificates.Terminal040.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_11, 194400000000, by norm_num, R7.Core.Certificates.Terminal040.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_12, 55112400000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_13, 499979692800000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_14, 185904945275522457600000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_14⟩
theorem bound_161 : minorBindings polynomial_161 witness_161 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_161 witness_161 (by decide +kernel)
theorem positive_161 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_161 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_161 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry026

namespace R7.Core.SpectralSliceCertificates.Entry027
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_162 : BiPoly := r7_rat_grid%[[1038689063622408960,60912663357482600400,202231560397373906400],[0,3441564676816944000,105375797939647800000],[10176768092049230160,976211558797976567400,2450593783998197001900],[0,69473100925693349400,601167691700462610000],[40048002964993524480,5284998991316474083500,9585116218622395078200],[0,104675088621353805000,1167244160510487375000],[79795719263222254800,11511037985371040083500,16086111860287996857000],[0,-58057765511856007500,888752281537167750000],[83654533517123675520,10682414643670642728000,11652739240661304076800],[0,-56221256246296377600,215727450304766400000],[42880262175119463840,3615453673910561505600,2849611614066844545600],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
noncomputable def witness_162 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_16, 1656000, by norm_num, R7.Core.Certificates.Terminal040.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_17, 66240000, by norm_num, R7.Core.Certificates.Terminal040.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_18, 1296000, by norm_num, R7.Core.Certificates.Terminal040.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_19, 349920000000, by norm_num, R7.Core.Certificates.Terminal040.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_20, 1574640000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_21, 422431822080000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_22, 67316018085189181440000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_22⟩
theorem bound_162 : minorBindings polynomial_162 witness_162 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_162 witness_162 (by decide +kernel)
theorem positive_162 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_162 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_162 ρ hρ u
noncomputable def polynomial_163 : BiPoly := r7_rat_grid%[[28951623384664320,666749777373604300,2643020197727488800],[0,1416007997261406000,5683071447997200000],[344620112426966880,18382130429480910700,56464063813451756700],[0,16508435756814549600,44691597317064240000],[1690390686581805600,176243252879191948125,320741498275882816500],[0,33351408772348122000,126420858591586200000],[4282433202016337400,563526942880120398000,756673438867862953500],[0,-1673403928738605000,146775102258467250000],[5831565406029212760,715824626446777441500,771335408964958538400],[0,-13900860060897456000,53339204745684000000],[3965552701154340660,334355980005956399400,263531155365937859400],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
noncomputable def witness_163 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal040.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_25, 1840000, by norm_num, R7.Core.Certificates.Terminal040.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal040.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_27, 4320000000, by norm_num, R7.Core.Certificates.Terminal040.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_28, 77760000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_29, 37791360000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_30, 752773506946560000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_30⟩
theorem bound_163 : minorBindings polynomial_163 witness_163 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_163 witness_163 (by decide +kernel)
theorem positive_163 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_163 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_163 ρ hρ u
noncomputable def polynomial_164 : BiPoly := r7_rat_grid%[[231216389496702720,6214186357821490300,23214858409390444800],[0,11221540896566982000,40340726825760900000],[2761150809597217920,159800936976753361300,474267794560450687800],[0,119268227471400836700,314284599676164105000],[13488503032808793360,1446508812993072904500,2632230040051257152400],[0,232245196951218921000,880631726098470975000],[34070660945901522000,4532470674215271412500,6118068956241416355000],[0,-12773218492911523500,1011577873255236450000],[46334190354817849920,5715518039268168888000,6168346817418691372800],[0,-95143664416809254400,365077223592681600000],[31550111600392776240,2660150873893543221600,2096665455878450661600],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
noncomputable def witness_164 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_0, 12098000, by norm_num, R7.Core.Certificates.Terminal041.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_1, 42320000, by norm_num, R7.Core.Certificates.Terminal041.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_2, 368000, by norm_num, R7.Core.Certificates.Terminal041.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_3, 496800000000, by norm_num, R7.Core.Certificates.Terminal041.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_4, 2235600000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_5, 4346006400000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_6, 692551626390835200000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_6⟩
theorem bound_164 : minorBindings polynomial_164 witness_164 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_164 witness_164 (by decide +kernel)
theorem positive_164 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_164 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_164 ρ hρ u
noncomputable def polynomial_165 : BiPoly := r7_rat_grid%[[895715635811840640,28790568170336486100,103929240111480057600],[0,40262210500332768000,134079813110001600000],[10526363722816707960,677874095247669903150,1932840664915735503900],[0,385979938813127257200,1015795446768103680000],[50566102604573928120,5644388593178284854000,10267130517370236280800],[0,709084157529792096000,2755411049330391600000],[125520777580542987600,16959319050013797897000,23056305237948471984000],[0,-47639133669784104000,3053294929750627800000],[167740491876639887520,20835372177629130618000,22535217541658500156800],[0,-276781569212536012800,1062042832269619200000],[112255645694215181760,9464846203245534998400,7459958859589625558400],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_165 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_8, 138000, by norm_num, R7.Core.Certificates.Terminal041.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_9, 24840000, by norm_num, R7.Core.Certificates.Terminal041.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_10, 54000, by norm_num, R7.Core.Certificates.Terminal041.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_11, 29160000000, by norm_num, R7.Core.Certificates.Terminal041.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_12, 44089920000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_13, 2399902525440000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_14, 1338515605983761694720000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_14⟩
theorem bound_165 : minorBindings polynomial_165 witness_165 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_165 witness_165 (by decide +kernel)
theorem positive_165 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_165 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_165 ρ hρ u
noncomputable def polynomial_166 : BiPoly := r7_rat_grid%[[2152632518165914560,82153670710148765025,289698189517039910400],[0,80987939826692478000,272071555832253600000],[24701091736159633680,1779135986177313962700,4880496977834641643700],[0,709112649358732206000,1970053680557516400000],[115457757124107399120,13481709638363628249000,24507942517146374920800],[0,1213320438455938281000,5066033068363664475000],[278306665948272155400,38278228556847029305500,52449984374785007886000],[0,-113906760479071560000,5284314181346854500000],[360344458165338964800,45115042365903969900000,48916377475514392032000],[0,-449770049970371020800,1725819602438131200000],[233052481821685866480,19649843748042360703200,15487523284582809583200],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
noncomputable def witness_166 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_16, 34500, by norm_num, R7.Core.Certificates.Terminal041.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_17, 12420000, by norm_num, R7.Core.Certificates.Terminal041.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_18, 1296000, by norm_num, R7.Core.Certificates.Terminal041.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_19, 349920000000, by norm_num, R7.Core.Certificates.Terminal041.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_20, 1763596800000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_21, 23999025254400000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_22, 26770312119675233894400000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_22⟩
theorem bound_166 : minorBindings polynomial_166 witness_166 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_166 witness_166 (by decide +kernel)
theorem positive_166 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_166 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_166 ρ hρ u
noncomputable def polynomial_167 : BiPoly := r7_rat_grid%[[3509516778182960400,157127605790165405375,541793430310152936000],[0,93502963891332240000,369438635852838000000],[38881711810695269700,3114751408988724183000,8252734826826242523000],[0,774907369364056812000,2515167058200967800000],[175006351443342837600,21368047987813078798125,38815136608059134446500],[0,1231199279368126920000,6014766251351738250000],[404771466879961029000,56669880069845330917500,78239160121443207547500],[0,-185052710609887365000,5777670766876611750000],[500861204768869232400,63192581906900360985000,68680146681392717016000],[0,-454094761989316896000,1742414021692344000000],[308092940628144928200,25976887677385843338000,20474343609199787538000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
noncomputable def witness_167 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal041.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_25, 34500000, by norm_num, R7.Core.Certificates.Terminal041.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_26, 54000000, by norm_num, R7.Core.Certificates.Terminal041.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_27, 24300000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_28, 15309000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_29, 520812180000000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_30, 726191192482509600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_30⟩
theorem bound_167 : minorBindings polynomial_167 witness_167 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_167 witness_167 (by decide +kernel)
theorem positive_167 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_167 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_167 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry027

namespace R7.Core.SpectralSliceCertificates.Entry028
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_168 : BiPoly := r7_rat_grid%[[3967363897650541440,205196732144532677475,689891359416507129600],[0,53780258066142762000,346334053496684400000],[42044963063021672760,3697290720538006631400,9513845961822995648400],[0,478409683420885556700,2189995075355007105000],[180067340426663062800,22878564665222891047500,41528003608389054402000],[0,719892225896580495000,4796057527135367625000],[394395792047821245600,56082465847045345684500,77926353907092515829000],[0,-200864349435718741500,4186908652489249050000],[459681075273896199360,58370395227777982944000,63563807095980430982400],[0,-302729841326211264000,1161609347794896000000],[264776903430920591760,22324691588090011898400,17595772527510312458400],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
noncomputable def witness_168 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_0, 103500, by norm_num, R7.Core.Certificates.Terminal042.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_1, 3651480000, by norm_num, R7.Core.Certificates.Terminal042.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_2, 23328000, by norm_num, R7.Core.Certificates.Terminal042.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_3, 6298560000000, by norm_num, R7.Core.Certificates.Terminal042.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_4, 1785641760000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_5, 170093091490560000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_6, 189734587148198220226560000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_6⟩
theorem bound_168 : minorBindings polynomial_168 witness_168 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_168 witness_168 (by decide +kernel)
theorem positive_168 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_168 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_168 ρ hρ u
noncomputable def polynomial_169 : BiPoly := r7_rat_grid%[[3068326757101076640,178291923418883309225,585894047729748297600],[0,3296789985064584000,223790638777840800000],[30600223402301186040,2896360557676189519350,7288607935061895581100],[0,135580179775643408400,1303306707273780960000],[122845579070583904920,16097307080598960177750,29201474129511639817800],[0,219727257820462368000,2608567336172242800000],[250801258308067022400,36075623319608780853000,50360060165377263291000],[0,-138139662738247128000,2071851698540087100000],[270947366794621429920,34558324520656300938000,37683944544625088572800],[0,-138390784606268006400,531021416134809600000],[143980067303449907040,12139694043293186193600,9568208102517128433600],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_169 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal042.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_9, 690000, by norm_num, R7.Core.Certificates.Terminal042.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_10, 54000, by norm_num, R7.Core.Certificates.Terminal042.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_11, 9720000000, by norm_num, R7.Core.Certificates.Terminal042.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_12, 4898880000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_13, 133327918080000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_14, 74361978110208983040000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_14⟩
theorem bound_169 : minorBindings polynomial_169 witness_169 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_169 witness_169 (by decide +kernel)
theorem positive_169 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_169 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_169 ρ hρ u
noncomputable def polynomial_170 : BiPoly := r7_rat_grid%[[76939930638696960,2364791498884715400,8428518412320326400],[0,3705005938347572000,11738960689181400000],[921780239926233600,57514943505886479000,165607692871095774000],[0,35489656296095092200,90345473605271430000],[4484626857654380640,494357200984203408000,899509364631817257600],[0,65893041241217622000,249965527821417450000],[11293952091890781600,1518908601796526547000,2060916800513309694000],[0,-4053068518638069000,282984976147578300000],[15338619153800665920,1901479688987372748000,2055336787705904812800],[0,-26360149448812953600,101146936406630400000],[10458600530516942400,881817969246478416000,695027222943132816000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_170 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_16, 828000, by norm_num, R7.Core.Certificates.Terminal042.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_17, 36800000, by norm_num, R7.Core.Certificates.Terminal042.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_18, 432000000, by norm_num, R7.Core.Certificates.Terminal042.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_19, 77760000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_20, 699840000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_21, 81629337600000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_22, 4335975400012185600000000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_22⟩
theorem bound_170 : minorBindings polynomial_170 witness_170 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_170 witness_170 (by decide +kernel)
theorem positive_170 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_170 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_170 ρ hρ u
noncomputable def polynomial_171 : BiPoly := r7_rat_grid%[[577446077370839040,20375725672867839600,69998675810926413600],[0,25496109480310988000,71588864239703100000],[6813841432636533600,457460239756136264000,1281197724365248524000],[0,223169243529730746300,543170351550912345000],[32808514498443976320,3719443264076515134000,6765795595207716868800],[0,393919870428011169000,1473856896401149275000],[81718094087373877200,11112294858731765266500,15153732896434757523000],[0,-23970195907007395500,1629360381690086850000],[109774585140034913280,13677245728446458592000,14807309825288952115200],[0,-147040208644159756800,564210254643235200000],[74023650421547692320,6241311626777852788800,4919248233497506708800],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_171 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_24, 552000, by norm_num, R7.Core.Certificates.Terminal042.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_25, 294400000, by norm_num, R7.Core.Certificates.Terminal042.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_26, 64000000, by norm_num, R7.Core.Certificates.Terminal042.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_27, 51840000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_28, 14696640000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_29, 133327918080000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_30, 49574652073472655360000000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_30⟩
theorem bound_171 : minorBindings polynomial_171 witness_171 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_171 witness_171 (by decide +kernel)
theorem positive_171 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_171 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_171 ρ hρ u
noncomputable def polynomial_172 : BiPoly := r7_rat_grid%[[2031967704264762240,82406542412241157600,278090296229474001600],[0,74590270283749290000,197873428917685500000],[23476066746848576640,1726165937224037539600,4686664343557100547600],[0,595284204244975712100,1446540301624038615000],[110364182296226560800,12978047932070685622500,23594294760800872347000],[0,981754830780715035000,3754077781711789125000],[267982483298922147600,36968180375525428579500,50729645246273241759000],[0,-67774535320761769500,3941158798092666150000],[350316972022739621760,43922960748085815144000,47645156521726066598400],[0,-335165181468305328000,1286067492201492000000],[229391971636004936640,19341207458806093257600,15244263756552713097600],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
noncomputable def witness_172 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal043.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_1, 721280000, by norm_num, R7.Core.Certificates.Terminal043.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_2, 1024000, by norm_num, R7.Core.Certificates.Terminal043.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_3, 276480000000, by norm_num, R7.Core.Certificates.Terminal043.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_4, 8709120000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_5, 474054819840000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_6, 528796288783708323840000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_6⟩
theorem bound_172 : minorBindings polynomial_172 witness_172 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_172 witness_172 (by decide +kernel)
theorem positive_172 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_172 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_172 ρ hρ u
noncomputable def polynomial_173 : BiPoly := r7_rat_grid%[[4340760519796588800,201058420116040699500,671123020019673492000],[0,111693717115453990000,319052594117875500000],[48479879493620348400,3909401434150718988500,10306777551186030043500],[0,826226456312422834500,2199813614750988675000],[219995183089839326400,26894739140742418162500,48860352318766366251000],[0,1263474791963070660000,5331126028613098500000],[513977804546610114000,71994870996466195755000,99432209104390909260000],[0,-125811377643117127500,5175117655169789250000],[644163364189788206400,81291300553231550460000,88356739394457598176000],[0,-407243715117403248000,1562641146438372000000],[402656120424902282400,33949991815989419016000,26758548083310613416000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
noncomputable def witness_173 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_8, 2070000, by norm_num, R7.Core.Certificates.Terminal043.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_9, 46000000, by norm_num, R7.Core.Certificates.Terminal043.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal043.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_11, 5400000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_12, 425250000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_13, 173604060000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_14, 322751641103337600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_14⟩
theorem bound_173 : minorBindings polynomial_173 witness_173 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_173 witness_173 (by decide +kernel)
theorem positive_173 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_173 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_173 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry028

namespace R7.Core.SpectralSliceCertificates.Entry029
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_174 : BiPoly := r7_rat_grid%[[6049104598282089600,316808958025030441500,1044218021176259064000],[0,76628416312597480000,323364044648713500000],[64726256222320215600,5676548781002369884000,14589678271920830716500],[0,572901543433928935500,2070336665248874325000],[279953137081367467200,35479260930961181122500,64409688937103661423000],[0,824496116517376740000,4588298591410066500000],[620652443226095232000,88154079211590792390000,122444686631770855380000],[0,-163651814089633485000,4053467443592952000000],[734469379743022056000,93212113811380483500000,101488617892096979040000],[0,-295521987961301472000,1133951982371208000000],[431126755202420625600,36350496287827054704000,28650566634655808304000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
noncomputable def witness_174 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_16, 6210000, by norm_num, R7.Core.Certificates.Terminal043.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_17, 46000000, by norm_num, R7.Core.Certificates.Terminal043.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_18, 2000000, by norm_num, R7.Core.Certificates.Terminal043.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_19, 3600000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_20, 8505000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_21, 771573600000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_22, 1434451738237056000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_22⟩
theorem bound_174 : minorBindings polynomial_174 witness_174 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_174 witness_174 (by decide +kernel)
theorem positive_174 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_174 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_174 ρ hρ u
noncomputable def polynomial_175 : BiPoly := r7_rat_grid%[[5559504885016773120,321979323736433276300,1048934783222949280800],[0,886557610368684000,211272655301448300000],[56008624350972398400,5256943913788925313500,13246507280074626418500],[0,120367418845157489400,1244954088048953610000],[227355510729967814880,29649386492213481178500,53794500533717098714200],[0,204037541032457277000,2535143307848533575000],[470552730393899358000,67543103032192295482500,94214823700056812595000],[0,-139684495537848145500,2062851795332524350000],[517089899447023432320,65890533137648248008000,71829407689295733388800],[0,-142715496625213881600,547615835389022400000],[280639114235537954400,23662115508113837496000,18649897148974063896000],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
noncomputable def witness_175 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal043.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal043.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal043.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_27, 2700000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_28, 85050000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_29, 11573604000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_30, 12910065644133504000000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_30⟩
theorem bound_175 : minorBindings polynomial_175 witness_175 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_175 witness_175 (by decide +kernel)
theorem positive_175 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_175 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_175 ρ hρ u
noncomputable def polynomial_176 : BiPoly := r7_rat_grid%[[154078160067699840,6049477713385667850,20249430683902635600],[0,6264294348047243000,15251250913784100000],[1793805296447358000,128078968742766793750,350785399658206657500],[0,49477723246698961800,113480596966231170000],[8556160248326822040,994596530315901603000,1808756409498178233600],[0,81647113041874746000,299488774513094100000],[21094630882878070800,2898057376221961176000,3970262047319086797000],[0,-4892228045887077000,319456482586781400000],[28044709050866291280,3511033408495326987000,3806815534159142635200],[0,-27389842786657209600,105097988610014400000],[18709274282369196960,1577474367207589166400,1243326476598270926400],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_176 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal044.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_1, 11500000, by norm_num, R7.Core.Certificates.Terminal044.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_2, 31250000, by norm_num, R7.Core.Certificates.Terminal044.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_3, 5625000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_4, 354375000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_5, 3214890000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_6, 298844112132720000000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_6⟩
theorem bound_176 : minorBindings polynomial_176 witness_176 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_176 witness_176 (by decide +kernel)
theorem positive_176 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_176 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_176 ρ hρ u
noncomputable def polynomial_177 : BiPoly := r7_rat_grid%[[1040870350315774080,44951018148243694825,147976943295965467200],[0,35920375521012360000,71018890265007000000],[11986547421063491640,912051206714706499600,2444491078190892710100],[0,254806946709017966400,517635958663541160000],[56151520023791520720,6697417401571954179000,12174699250363091802300],[0,391946479691210829000,1327535021647097775000],[135827796168963070200,18851467220533761511500,25938959172321040893000],[0,-14055591065210887500,1358705103580440000000],[176859053836722915840,22239464966334177786000,24145866595217932185600],[0,-109198978478383348800,419009086168873200000],[115306070848949289960,9722043110942424536400,7662675132948039296400],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_177 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal044.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal044.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal044.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_11, 4320000000, by norm_num, R7.Core.Certificates.Terminal044.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_12, 136080000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_13, 24998984640000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_14, 13942870895664184320000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_14⟩
theorem bound_177 : minorBindings polynomial_177 witness_177 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_177 witness_177 (by decide +kernel)
theorem positive_177 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_177 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_177 ρ hρ u
noncomputable def polynomial_178 : BiPoly := r7_rat_grid%[[3254826769383794400,156323028470501493500,511441413674701746000],[0,79555959016060215000,131484596643220500000],[36330449314251709800,2978107550778673234500,7798783250902565007000],[0,500983646394463056000,912440242460381400000],[164848732709214216600,20286617376152249805000,36854365181982133869000],[0,704912056504678440000,2202933547856011500000],[385161527267521488000,54106119872586415710000,74821812052520505982500],[0,-7343740752477570000,2083097762616417750000],[482902622130442046400,61024468310010637110000,66356350455089743776000],[0,-151364920663105632000,580804673897448000000],[301992090318676711800,25462493861992064262000,20068911062482960062000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
noncomputable def witness_178 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_16, 230000, by norm_num, R7.Core.Certificates.Terminal044.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_17, 138000000, by norm_num, R7.Core.Certificates.Terminal044.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_18, 18000000, by norm_num, R7.Core.Certificates.Terminal044.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_19, 24300000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_20, 1653372000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_21, 506229438960000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_22, 705857839092999331200000000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_22⟩
theorem bound_178 : minorBindings polynomial_178 witness_178 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_178 witness_178 (by decide +kernel)
theorem positive_178 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_178 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_178 ρ hρ u
noncomputable def polynomial_179 : BiPoly := r7_rat_grid%[[5933099805953126400,315398480684377932875,1027218974127496626000],[0,71637135903095555000,102325882744341000000],[63630332840476099800,5605970976912875072000,14373328488022371357000],[0,397946089910852199000,662150079138821850000],[275808624976314486000,35006496909465421338750,63553215937901550615000],[0,501655344723805320000,1437812447575347000000],[613100256416928144000,87136217987670433305000,121068313335979896960000],[0,7945403177765970000,1201720392150358500000],[728018950060648209600,92419830590254598340000,100634725593408543264000],[0,-75682460331552816000,290402336948724000000],[429093138432597886800,36179031682695795012000,28515422452416865812000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
noncomputable def witness_179 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal044.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_25, 23000000, by norm_num, R7.Core.Certificates.Terminal044.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_26, 8000000, by norm_num, R7.Core.Certificates.Terminal044.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_27, 21600000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_28, 27216000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_29, 14196954240000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_30, 26393911983561830400000000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_30⟩
theorem bound_179 : minorBindings polynomial_179 witness_179 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_179 witness_179 (by decide +kernel)
theorem positive_179 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_179 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_179 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry029

namespace R7.Core.SpectralSliceCertificates.Entry030
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_180 : BiPoly := r7_rat_grid%[[6729517322519277600,389335390441844805250,1264334570488808484000],[0,0,0],[67997004857740288800,6364054140630174557000,16042718803901916492000],[0,0,0],[277010227994487094800,36063989682361519440000,65436660998625647907000],[0,0,0],[575854244198990460000,82595556865471533300000,115179539292121828275000],[0,0,0],[636320228098720006800,81054375665317825995000,88350369436070508312000],[0,0,0],[347748467639688334800,29320447477445407332000,23109655162859166132000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
noncomputable def witness_180 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_0, 115000, by norm_num, R7.Core.Certificates.Terminal045.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_1, 2254000000, by norm_num, R7.Core.Certificates.Terminal045.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_2, 784000000, by norm_num, R7.Core.Certificates.Terminal045.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_3, 10584000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_4, 13335840000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_5, 51720121555200000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_6, 72115626688129753344000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_6⟩
theorem bound_180 : minorBindings polynomial_180 witness_180 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_180 witness_180 (by decide +kernel)
theorem positive_180 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_180 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_180 ρ hρ u
noncomputable def polynomial_181 : BiPoly := r7_rat_grid%[[231454348045069824,10721034003234676510,34891460497703024160],[0,6850996990748252400,10106055009461880000],[2642052612688567056,211125720194562447340,556853951686509095040],[0,42549510787568432400,70877667105939060000],[12193215711524421840,1485451124249699748000,2699372008747422840600],[0,58802056226234636400,171627479243126190000],[29017561408131543120,4062918036747151193400,5611269212145512200800],[0,248437228980137400,160134262328038320000],[37089970673649616800,4682545896339278730000,5090167997096201712000],[0,-10811780047364688000,41486048135532000000],[23671299200736679632,1995848003727862814880,1573078281261290606880],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
noncomputable def witness_181 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_8, 1209800, by norm_num, R7.Core.Certificates.Terminal045.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_9, 36800, by norm_num, R7.Core.Certificates.Terminal045.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_10, 128, by norm_num, R7.Core.Certificates.Terminal045.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_11, 13824000, by norm_num, R7.Core.Certificates.Terminal045.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_12, 4354560000000, by norm_num, R7.Core.Certificates.Terminal045.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_13, 11851370496000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_14, 1321990721959270809600000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_14⟩
theorem bound_181 : minorBindings polynomial_181 witness_181 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_181 witness_181 (by decide +kernel)
theorem positive_181 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_181 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_181 ρ hρ u
noncomputable def polynomial_182 : BiPoly := r7_rat_grid%[[1401377551091936640,70096770907549959850,227239428433728447600],[0,30251410713132597000,13739025988098900000],[15528854610120924000,1307044333216415402500,3393691142777452597500],[0,154003049540733482400,94823129884471560000],[69851831046244299360,8700169565784596243250,15802377074782290504900],[0,185669073774405873000,210105924931118925000],[161548141472455982400,22811315083346953345500,31612799180505706191000],[0,29079010692687406500,144934139480816700000],[200080600693268762880,25344224236864513512000,27578613763652940979200],[0,-1081178004736468800,4148604813553200000],[123237176251257971280,10390755070954337335200,8189737443679915015200],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_182 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal045.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_17, 23000000, by norm_num, R7.Core.Certificates.Terminal045.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_18, 250000000, by norm_num, R7.Core.Certificates.Terminal045.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_19, 67500000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_20, 2126250000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_21, 28934010000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_22, 16137582055166880000000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_22⟩
theorem bound_182 : minorBindings polynomial_182 witness_182 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_182 witness_182 (by decide +kernel)
theorem positive_182 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_182 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_182 ρ hρ u
noncomputable def polynomial_183 : BiPoly := r7_rat_grid%[[3736048358758685760,202131588186809836150,655874964401543318400],[0,40444605767084598000,-67200721599677400000],[39930891507077217120,3560226511301345859300,9095472166194802428300],[0,135720220896467781000,-424276195185734850000],[172136760506723844720,21973530912711028816500,39887951668958155024800],[0,108210824339190597000,-987654599038631925000],[380132457415053404400,54160525039960608070500,75326605498901900421000],[0,105211749968201992500,-964818566002194750000],[447718460226584702400,56901776386010193540000,61981228469023014816000],[0,84331884369444566400,-323591175457149600000],[261116393245239661920,22016055298853744452800,17352512999480215972800],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
noncomputable def witness_183 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal045.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_25, 8280000, by norm_num, R7.Core.Certificates.Terminal045.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_26, 144000, by norm_num, R7.Core.Certificates.Terminal045.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_27, 38880000000, by norm_num, R7.Core.Certificates.Terminal045.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_28, 18370800000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_29, 499979692800000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_30, 557714835826567372800000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_30⟩
theorem bound_183 : minorBindings polynomial_183 witness_183 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_183 witness_183 (by decide +kernel)
theorem positive_183 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_183 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_183 ρ hρ u
noncomputable def polynomial_184 : BiPoly := r7_rat_grid%[[274247226993087360,14431395299821089525,46670259063156962400],[0,4374639412087322000,-3842037178518600000],[2974574359466502120,259743344243336428050,667185421187059953300],[0,15876424190604133800,-27457012626792030000],[13122930589144414920,1662180585053448957750,3017982350971244467800],[0,12887977736273094000,-72987591058898850000],[29668079317375708200,4218006663826358454000,5861542050047308563000],[0,9485972540079021000,-85133838779759700000],[35785224669714906960,4545953165338772229000,4951064590304145566400],[0,8649424037891750400,-33188838508425600000],[21352976083138757400,1800378353878226766000,1419013913508896166000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_184 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_0, 103500, by norm_num, R7.Core.Certificates.Terminal046.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_1, 230000, by norm_num, R7.Core.Certificates.Terminal046.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_2, 18000, by norm_num, R7.Core.Certificates.Terminal046.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_3, 9720000000, by norm_num, R7.Core.Certificates.Terminal046.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_4, 612360000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_5, 479147205600000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_6, 44539726472260588800000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_6⟩
theorem bound_184 : minorBindings polynomial_184 witness_184 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_184 witness_184 (by decide +kernel)
theorem positive_184 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_184 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_184 ρ hρ u
noncomputable def polynomial_185 : BiPoly := r7_rat_grid%[[1404252883551372480,77600912047230781450,252503305581357823200],[0,11152387320509512000,-68608025543640600000],[14846946728084585280,1349564245727442881700,3430585129210707287700],[0,2120004854040725400,-430705511827947990000],[63122175272716010640,8135055027752562348000,14763855172764793332600],[0,-37378086506603829000,-965597320790185275000],[137072190586382647200,19608202151476455181500,27313691450971377573000],[0,66756975881670931500,-878077434463919550000],[158152807757838761280,20134809837874727352000,21943689180715516435200],[0,67753821630152044800,-259979234982667200000],[89885861226165054960,7578735546801678386400,5973372854961258146400],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_185 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal046.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal046.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal046.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal046.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_12, 1224720000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_13, 5555329920000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_14, 2065610503061360640000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_14⟩
theorem bound_185 : minorBindings polynomial_185 witness_185 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_185 witness_185 (by decide +kernel)
theorem positive_185 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_185 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_185 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry030

namespace R7.Core.SpectralSliceCertificates.Entry031
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_186 : BiPoly := r7_rat_grid%[[244502408447199360,13925177556453886400,45475082130012542400],[0,686602427524248000,-17406843196172400000],[2542228002614737440,237165016354505721600,598918367667596394600],[0,-8466526722047869200,-107368996164103980000],[10536089741264908800,1374483959327332695000,2493682991663515542000],[0,-18044011994042862000,-234177753906396450000],[22210294843323208800,3192053949663925221000,4454459243107645842000],[0,13652865943289397000,-202231359115542900000],[24737816690973984960,3155115287770623684000,3440445714316350086400],[0,14415706729819584000,-55314730847376000000],[13479974017110725760,1136565382584349958400,895812865126704518400],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_186 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_16, 736000, by norm_num, R7.Core.Certificates.Terminal046.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_17, 176640000, by norm_num, R7.Core.Certificates.Terminal046.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_18, 3456000, by norm_num, R7.Core.Certificates.Terminal046.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_19, 622080000000, by norm_num, R7.Core.Certificates.Terminal046.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_20, 128770560000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_21, 29023764480000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_22, 1541680142226554880000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_22⟩
theorem bound_186 : minorBindings polynomial_186 witness_186 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_186 witness_186 (by decide +kernel)
theorem positive_186 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_186 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_186 ρ hρ u
noncomputable def polynomial_187 : BiPoly := r7_rat_grid%[[1850788709521920,33119501361543300,133322006904172800],[0,102191307402573000,416583000192600000],[24091983543526560,1177706157508260900,3753201545309052900],[0,1265214174391194300,3435718776426045000],[120839173578940320,12265772961740470875,22323950755853316300],[0,2689306098977331000,10127256302285100000],[311813773560307800,40572351854457223500,54175549845463002000],[0,-121060378256953500,12223204031693700000],[431424842392536480,52679216839017177000,56668980714916003200],[0,-1181287079249104800,4532734888882200000],[295358626093302540,24903192650016288600,19628083610894028600],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
noncomputable def witness_187 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal046.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_25, 49680000, by norm_num, R7.Core.Certificates.Terminal046.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_26, 3888000, by norm_num, R7.Core.Certificates.Terminal046.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_27, 349920000000, by norm_num, R7.Core.Certificates.Terminal046.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_28, 1574640000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_29, 85030560000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_30, 125462251157760000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_30⟩
theorem bound_187 : minorBindings polynomial_187 witness_187 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_187 witness_187 (by decide +kernel)
theorem positive_187 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_187 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_187 ρ hρ u
noncomputable def polynomial_188 : BiPoly := r7_rat_grid%[[15467305643861760,346025449462032400,1229048592594158400],[0,797634657827122000,3129997666766400000],[197973256075066080,10116159750425741200,31463585260247122200],[0,9742621686330808200,25974004027831830000],[1004051335523891760,103207447422521168250,187869505303327883400],[0,20658664272577410000,77471341819236000000],[2626101322278555600,343603996667252577000,460134842201189604000],[0,-982351423860057000,95048672127467400000],[3694336999905021120,452265303299605938000,486921040098585580800],[0,-9421694041274942400,36152127660963600000],[2585598464488910760,218004997952601608400,171826174560941168400],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_188 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_0, 184000, by norm_num, R7.Core.Certificates.Terminal047.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_1, 14720000, by norm_num, R7.Core.Certificates.Terminal047.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal047.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_3, 23040000000, by norm_num, R7.Core.Certificates.Terminal047.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_4, 1866240000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_5, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_6, 8029584074096640000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_6⟩
theorem bound_188 : minorBindings polynomial_188 witness_188 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_188 witness_188 (by decide +kernel)
theorem positive_188 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_188 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_188 ρ hρ u
noncomputable def polynomial_189 : BiPoly := r7_rat_grid%[[63257314107588480,1725174097523561450,5852576441775763200],[0,3099348465907361000,11178440905880700000],[798439758958831320,44914208815951912300,134100847992259581300],[0,34897923797299601100,91455795185758965000],[4022315187950682000,426597632034241897500,776430681282865755000],[0,71630899256549124000,270087198300601650000],[10470077167254372000,1386457319316945195000,1867508646409531980000],[0,-3876163869472803000,328248875277872100000],[14685199004157600960,1807363440495754884000,1949151790152379526400],[0,-32435340142094064000,124458144406596000000],[10284290521674993360,867121003092370442400,683443435894080602400],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_189 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal047.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_9, 2760000, by norm_num, R7.Core.Certificates.Terminal047.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal047.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_11, 43200000000, by norm_num, R7.Core.Certificates.Terminal047.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_12, 388800000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_13, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_14, 40147920370483200000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_14⟩
theorem bound_189 : minorBindings polynomial_189 witness_189 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_189 witness_189 (by decide +kernel)
theorem positive_189 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_189 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_189 ρ hρ u
noncomputable def polynomial_190 : BiPoly := r7_rat_grid%[[164819344542603840,5362171085153516600,18058305641488245600],[0,7280154003893884000,24841673491375800000],[2034201393109938240,128161001674649268600,366785662785663216600],[0,74648253752314932000,197169294195145800000],[10071741456276171840,1114145977616534883000,2026959189866875965600],[0,145330412774032818000,564865123555894050000],[25757534102174416800,3467616471984586671000,4706611221712379562000],[0,-10087152913615869000,663711165517938300000],[35477363253056155200,4399000124311695420000,4755276958586460768000],[0,-63429109611206169600,243384815728454400000],[24403401237872865600,2057575261575116304000,1621730186867309904000],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
noncomputable def witness_190 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_16, 92000, by norm_num, R7.Core.Certificates.Terminal047.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_17, 7360000, by norm_num, R7.Core.Certificates.Terminal047.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_18, 384000, by norm_num, R7.Core.Certificates.Terminal047.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_19, 69120000000, by norm_num, R7.Core.Certificates.Terminal047.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_20, 21772800000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_21, 5925685248000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_22, 734439289977372672000000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_22⟩
theorem bound_190 : minorBindings polynomial_190 witness_190 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_190 witness_190 (by decide +kernel)
theorem positive_190 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_190 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_190 ρ hρ u
noncomputable def polynomial_191 : BiPoly := r7_rat_grid%[[298637978200715520,11438675800749541050,38495228763653596800],[0,10690662685386342000,37760116013667900000],[3584599094951775180,253436259801903377700,697387342105364753700],[0,101617613529557645400,286510510825325010000],[17268461001839915280,2001233869344677115375,3638527145552584937700],[0,185797080851786037000,781724893732804575000],[42892988263883074800,5883257591689170568500,8051748330545236782000],[0,-18857342829074715000,868368490008925500000],[57232903363607946240,7156983521015218926000,7757142493305658521600],[0,-78205209009271243200,300082414847014800000],[38028633595685215560,3206388115954556240400,2527196207868224600400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_191 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_24, 69000, by norm_num, R7.Core.Certificates.Terminal047.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_25, 1713960000, by norm_num, R7.Core.Certificates.Terminal047.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_26, 268272000, by norm_num, R7.Core.Certificates.Terminal047.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_27, 24144480000000, by norm_num, R7.Core.Certificates.Terminal047.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_28, 3042204480000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_29, 6899719760640000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_30, 1282744122401104957440000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_30⟩
theorem bound_191 : minorBindings polynomial_191 witness_191 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_191 witness_191 (by decide +kernel)
theorem positive_191 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_191 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_191 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry031

namespace R7.Core.SpectralSliceCertificates.Entry032
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_192 : BiPoly := r7_rat_grid%[[390549467507509440,17383119188485668100,58228257923098749600],[0,9361998940438356000,40856053588837200000],[4516985045024887320,355860355549897384800,945843451431122683800],[0,86970583699249005600,291974904534230640000],[20960844513614389440,2543058516317366016750,4620135700094627424600],[0,149853927313857168000,746010029023654050000],[49981745427942182400,6983560569940391358000,9633381094371977316000],[0,-25182574801813170000,768150367888081500000],[63741973315821554880,8036646248495832912000,8732689506243090259200],[0,-64149894947697148800,246150552270823200000],[40265612042490228240,3394999181598941901600,2675854808331061341600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_192 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal048.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_1, 11040000, by norm_num, R7.Core.Certificates.Terminal048.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_2, 10368000, by norm_num, R7.Core.Certificates.Terminal048.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_3, 11197440000000, by norm_num, R7.Core.Certificates.Terminal048.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_4, 1410877440000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_5, 57597660610560000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_6, 10708124847870093557760000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_6⟩
theorem bound_192 : minorBindings polynomial_192 witness_192 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_192 witness_192 (by decide +kernel)
theorem positive_192 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_192 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_192 ρ hρ u
noncomputable def polynomial_193 : BiPoly := r7_rat_grid%[[368538301783552320,18796060964752976800,62218936590538408800],[0,3750723695512749000,31697989663101300000],[4072592696401359360,352632240239900352900,910442057845532004900],[0,42552765427897107900,211171410623819385000],[17992138299790198320,2273798951582264090250,4127824040009505598800],[0,71955169189244478000,498747321848661300000],[40655938989349490400,5773264022150043588000,8017401680723101536000],[0,-23076801719853903000,470405747572217100000],[48847344776521945920,6200834623014119508000,6751943473779556012800],[0,-36279528603379286400,139208739299229600000],[28877358131482890960,2434797392863887626400,1919047387792983386400],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
noncomputable def witness_193 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_8, 2576000, by norm_num, R7.Core.Certificates.Terminal048.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_9, 11040000, by norm_num, R7.Core.Certificates.Terminal048.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_10, 144000, by norm_num, R7.Core.Certificates.Terminal048.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_11, 103680000000, by norm_num, R7.Core.Certificates.Terminal048.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_12, 11430720000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_13, 7407106560000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_14, 918049112471715840000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_14⟩
theorem bound_193 : minorBindings polynomial_193 witness_193 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_193 witness_193 (by decide +kernel)
theorem positive_193 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_193 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_193 ρ hρ u
noncomputable def polynomial_194 : BiPoly := r7_rat_grid%[[14277512902026240,393975386670175100,1258199123050761600],[0,675547549031087000,2510748331799400000],[179118660258393120,9632964083277134300,29148356612712768300],[0,8098315803140867700,21026539067829255000],[920550108837320640,96022938189378098625,174823453803975920100],[0,17113573654358841000,63797376917906100000],[2445878682514341000,322056826644390142500,432689735793212190000],[0,-875159443407532500,80088507969691500000],[3505850418277213920,430417655048057283000,463821253762927132800],[0,-8211804369307941600,31509641321987400000],[2512969294138098660,211881262055056619400,166999596623836079400],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_194 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal048.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal048.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal048.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_19, 7200000000, by norm_num, R7.Core.Certificates.Terminal048.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_20, 291600000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_21, 47239200000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_22, 627311255788800000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_22⟩
theorem bound_194 : minorBindings polynomial_194 witness_194 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_194 witness_194 (by decide +kernel)
theorem positive_194 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_194 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_194 ρ hρ u
noncomputable def polynomial_195 : BiPoly := r7_rat_grid%[[111443920151927040,3411822885012767100,10534903726444833600],[0,4943599807941959000,17273778498528300000],[1405714865887506240,80580742606709176100,237131868678379649100],[0,55966548011964357300,143603151157066995000],[7211654724320691120,767968442619145265250,1398108204510202450800],[0,116074836863655876000,433565638169923350000],[19172256058726448400,2545090046467984953000,3433044230780657256000],[0,-6460312263478101000,542166421156040700000],[27552549643282572480,3395651853913594632000,3663634147163836243200],[0,-55740732688635724800,213883625943187200000],[19871341007982190560,1675454141568308990400,1320551723591952350400],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
noncomputable def witness_195 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal048.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_25, 1840000, by norm_num, R7.Core.Certificates.Terminal048.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal048.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_27, 66240000000, by norm_num, R7.Core.Certificates.Terminal048.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_28, 25920000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_29, 302330880000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_30, 32118336296386560000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_30⟩
theorem bound_195 : minorBindings polynomial_195 witness_195 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_195 witness_195 (by decide +kernel)
theorem positive_195 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_195 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_195 ρ hρ u
noncomputable def polynomial_196 : BiPoly := r7_rat_grid%[[425152606415892480,14840499219534756450,46113968002975873200],[0,16596954717684228000,55060833492341100000],[5277977481736715400,332657101943130583500,945423331199222323500],[0,173159433190206400800,446387876856821520000],[26673550388146877040,2942220759298672041750,5354306012136865683600],[0,343613790125806095000,1312607185260940125000],[69857727984795564000,9400066595221978597500,12759336845540241885000],[0,-23146593368613025500,1595454408649202850000],[98926135219678898880,12266829418555780992000,13260503780166235219200],[0,-159533821143336729600,612149688044294400000],[70363140235866762480,5932675337541585343200,4675988705467410223200],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_196 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_0, 207000, by norm_num, R7.Core.Certificates.Terminal049.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_1, 124200000, by norm_num, R7.Core.Certificates.Terminal049.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_2, 54000000, by norm_num, R7.Core.Certificates.Terminal049.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_3, 24300000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_4, 765450000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_5, 79857867600000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_6, 29693150981507059200000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_6⟩
theorem bound_196 : minorBindings polynomial_196 witness_196 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_196 witness_196 (by decide +kernel)
theorem positive_196 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_196 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_196 ρ hρ u
noncomputable def polynomial_197 : BiPoly := r7_rat_grid%[[1009043394471673920,40035217004637804550,126823728338587852800],[0,30784282265385250000,106027254145575000000],[12239775117656863200,855660952142279898000,2350286621059458438000],[0,300409751418232516200,823683484580802030000],[60283812437134272000,6935252090939394750000,12613064358186946980000],[0,563548605637238298000,2310838332171727050000],[153635509383760465200,21019749959556410409000,28742021648387185068000],[0,-53845496311545666000,2665765090661236200000],[211280892232663350720,26395676261840406528000,28600695801280769644800],[0,-252274867771842720000,968007789829080000000],[145606960719308098080,12276865727398193947200,9676323448308282427200],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
noncomputable def witness_197 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal049.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_9, 901600000, by norm_num, R7.Core.Certificates.Terminal049.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_10, 288000000, by norm_num, R7.Core.Certificates.Terminal049.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_11, 51840000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_12, 901393920000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_13, 355541114880000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_14, 264398144391854161920000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_14⟩
theorem bound_197 : minorBindings polynomial_197 witness_197 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_197 witness_197 (by decide +kernel)
theorem positive_197 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_197 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_197 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry032

namespace R7.Core.SpectralSliceCertificates.Entry033
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_198 : BiPoly := r7_rat_grid%[[1629024562363132800,73032777293242959500,235382147932413702000],[0,30446607709491800000,134834746587660000000],[19089623590915515300,1475979747968868942000,3930837202642224064500],[0,297004792932682614000,986130407746641600000],[90680295566331198000,10891376310118247795625,19793230228744316257500],[0,530775383465447820000,2589751272029331375000],[222188768737881714000,30926912512272367680000,42600252145603224510000],[0,-86938862885435925000,2774823639671553750000],[292614946500413577600,36836215876947773790000,40007537988967128384000],[0,-244466359959857112000,938045643953418000000],[192176784748248816600,16203405184904040894000,12771125221580065494000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
noncomputable def witness_198 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_16, 230000, by norm_num, R7.Core.Certificates.Terminal049.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_17, 46000000, by norm_num, R7.Core.Certificates.Terminal049.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_18, 6000000, by norm_num, R7.Core.Certificates.Terminal049.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_19, 97200000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_20, 15309000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_21, 4687309620000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_22, 4357147154895057600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_22⟩
theorem bound_198 : minorBindings polynomial_198 witness_198 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_198 witness_198 (by decide +kernel)
theorem positive_198 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_198 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_198 ρ hρ u
noncomputable def polynomial_199 : BiPoly := r7_rat_grid%[[1826629306902982080,91815624814539447950,298221936553798687200],[0,9055854326898019000,116484865212750300000],[20498611824132305040,1733830693738572488100,4497840547795279916100],[0,140768911911928644900,791974811423170935000],[92806521923911204080,11593615629244635939750,21053610758685508117200],[0,259620799603569264000,1917701668816608150000],[215769409950089689200,30503097437940697329000,42287007604020351228000],[0,-95323999163465331000,1886055958164476700000],[268161953977232723520,33980263056218045448000,36980064606375172396800],[0,-154728585566730201600,593711444428502400000],[165129681709606390560,13922925936658286990400,10973707597802130350400],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
noncomputable def witness_199 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal049.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_25, 920000, by norm_num, R7.Core.Certificates.Terminal049.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal049.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_27, 8640000000, by norm_num, R7.Core.Certificates.Terminal049.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_28, 544320000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_29, 34566497280000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_30, 25705375149208043520000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_30⟩
theorem bound_199 : minorBindings polynomial_199 witness_199 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_199 witness_199 (by decide +kernel)
theorem positive_199 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_199 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_199 ρ hρ u
noncomputable def polynomial_200 : BiPoly := r7_rat_grid%[[54333868543822080,1835921338332066700,5502107234241787200],[0,2241409611817611000,7230785171330700000],[689240224853933760,42048886273600638900,120538442227528575900],[0,23573284799400886500,59496994885749975000],[3529454288971408560,383876689861632870750,698814389294298770400],[0,47620542246220512000,178376130498298950000],[9388741328669084400,1256862739890424383000,1702285287607808496000],[0,-2959674489847971000,221812389277274700000],[13529147970173716800,1673981233721365500000,1808349132112127712000],[0,-22893515211403958400,87845060655237600000],[9819463831429795920,827929093348082512800,652553337096608032800],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_200 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal050.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_1, 5520000, by norm_num, R7.Core.Certificates.Terminal050.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_2, 144000, by norm_num, R7.Core.Certificates.Terminal050.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_3, 25920000000, by norm_num, R7.Core.Certificates.Terminal050.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_4, 1166400000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_5, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_6, 40147920370483200000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_6⟩
theorem bound_200 : minorBindings polynomial_200 witness_200 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_200 witness_200 (by decide +kernel)
theorem positive_200 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_200 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_200 ρ hρ u
noncomputable def polynomial_201 : BiPoly := r7_rat_grid%[[401753349159793920,15005654415651683300,44738488759538902800],[0,14257288838990832000,42323334393105900000],[5012703793371580560,324886009657601310900,910770356685561912900],[0,139885933499008102800,344225393421767820000],[25463800908834114960,2834749058751277107000,5159103624084924221400],[0,272141320442994369000,1016304940632019275000],[67162970418797307600,9073562427455298034500,12340939583848710159000],[0,-17588278170644422500,1240794846013920750000],[95994121727690786880,11928128290423894332000,12902809029272661139200],[0,-125176386770600054400,480316246191381600000],[69142970173973119200,5829796574462829528000,4594902196124044728000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_201 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_8, 46000, by norm_num, R7.Core.Certificates.Terminal050.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_9, 5520000, by norm_num, R7.Core.Certificates.Terminal050.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_10, 144000, by norm_num, R7.Core.Certificates.Terminal050.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal050.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_12, 408240000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_13, 18517766400000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_14, 6885368343537868800000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_14⟩
theorem bound_201 : minorBindings polynomial_201 witness_201 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_201 witness_201 (by decide +kernel)
theorem positive_201 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_201 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_201 ρ hρ u
noncomputable def polynomial_202 : BiPoly := r7_rat_grid%[[1396717529519747520,57708966259039050425,175640961504209476800],[0,37666818618422694000,109797446962747800000],[17071265295679309200,1202565086344214770500,3282275919805429765500],[0,344321015242025074200,862956253763887230000],[84802623853710606480,9766677498329735271000,17765159326992428083200],[0,634365526407775749000,2451208879574054775000],[218472749546552908200,29909288436147229216500,40916607874745403438000],[0,-49676092562707884000,2863844359016923800000],[304518921277885312320,38062046181913357968000,41247701967425308588800],[0,-274619213203063075200,1053745622642512800000],[213529760831387574000,18003783538782267660000,14190139135088961660000],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
noncomputable def witness_202 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_16, 11500, by norm_num, R7.Core.Certificates.Terminal050.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_17, 20700000, by norm_num, R7.Core.Certificates.Terminal050.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_18, 18000000, by norm_num, R7.Core.Certificates.Terminal050.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_19, 4860000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_20, 88179840000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_21, 29998781568000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_22, 33462890149594042368000000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_22⟩
theorem bound_202 : minorBindings polynomial_202 witness_202 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_202 witness_202 (by decide +kernel)
theorem positive_202 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_202 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_202 ρ hρ u
noncomputable def polynomial_203 : BiPoly := r7_rat_grid%[[2956139216485502400,134688472768798151000,421554290566224216000],[0,45431459105326280000,160478687545461000000],[34943850913567219200,2686753778916686238000,7146845613902499228000],[0,406872429988126983000,1190605276439586450000],[167817099487157568000,20069980710227516452500,36480791040126975495000],[0,714739467482323560000,3179268661350219750000],[416743399378583856000,57907565211668549445000,79718321489687258040000],[0,-92355157814687460000,3467074421602984500000],[557962167525337713600,70190194952162147940000,76216456468552254624000],[0,-311139003585272688000,1193876274122532000000],[374185485647383939200,31549487344151783328000,24866529531965418528000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
noncomputable def witness_203 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_24, 460000, by norm_num, R7.Core.Certificates.Terminal050.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_25, 368000000, by norm_num, R7.Core.Certificates.Terminal050.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_26, 2304000000, by norm_num, R7.Core.Certificates.Terminal050.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_27, 2073600000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_28, 114960384000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_29, 1896219279360000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_30, 3525308591891388825600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_30⟩
theorem bound_203 : minorBindings polynomial_203 witness_203 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_203 witness_203 (by decide +kernel)
theorem positive_203 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_203 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_203 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry033
