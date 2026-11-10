import R7.Spectral.SliceInteger
import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch01
import R7.Certificates.Spectral.Terminal.Batches.Batch02
import R7.Certificates.Spectral.Terminal.Batches.Batch03
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.Entry010
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_60 : BiPoly := r7_rat_grid%[[1841283587506589568,112334958967136031320,367010884173152241120],[0,12962510804311945200,82847412917953740000],[14920898642787758112,1451951129754723057180,3623171225612222350080],[0,67336553204279543100,336410095140986265000],[48903206224340139840,6466979131675302535500,11729887739394234960600],[0,64106824531380777000,481211608997402325000],[82301672158991334000,11867726312985771945000,16584225557094330435000],[0,-15075841953813070500,280998548873434350000],[74238581617138995840,9474487578346678776000,10333265032460183385600],[0,-14055314061574094400,53931862576191600000],[33432659695885825872,2818878108357909336480,2221770356008214568480],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
noncomputable def witness_60 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_0, 18400, by norm_num, R7.Core.Certificates.Terminal015.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_1, 441600, by norm_num, R7.Core.Certificates.Terminal015.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_2, 3456, by norm_num, R7.Core.Certificates.Terminal015.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_3, 3110400000, by norm_num, R7.Core.Certificates.Terminal015.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_4, 146966400000000, by norm_num, R7.Core.Certificates.Terminal015.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_5, 399983754240000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_6, 44617186866125389824000000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_6⟩
theorem bound_60 : minorBindings polynomial_60 witness_60 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_60 witness_60 (by decide +kernel)
theorem positive_60 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_60 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_60 ρ hρ u
noncomputable def polynomial_61 : BiPoly := r7_rat_grid%[[1043567213863934592,69019413972803804580,221015619963636533280],[0,-358766499906020400,36977580280474020000],[7774064098477872624,786906989020110155360,1941016698948277901160],[0,9798149996068221300,140115518323771095000],[23251357837520820000,3118638578346247102500,5655014112779786925000],[0,11109008847982311000,187180426170452475000],[35666918612384565600,5166933590630703627000,7233609983538116754000],[0,-7656352959364861500,102433269488514300000],[29378775189720882240,3755422117732781916000,4097809770953920761600],[0,-4925366466021691200,18899199706186800000],[12120355948143523248,1021929046582307764320,805459326144097252320],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_61 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_8, 193200, by norm_num, R7.Core.Certificates.Terminal015.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_9, 441600, by norm_num, R7.Core.Certificates.Terminal015.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_10, 1024, by norm_num, R7.Core.Certificates.Terminal015.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_11, 184320000, by norm_num, R7.Core.Certificates.Terminal015.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_12, 8709120000000, by norm_num, R7.Core.Certificates.Terminal015.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_13, 7900913664000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_14, 293775715990949068800000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_14⟩
theorem bound_61 : minorBindings polynomial_61 witness_61 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_61 witness_61 (by decide +kernel)
theorem positive_61 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_61 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_61 ρ hρ u
noncomputable def polynomial_62 : BiPoly := r7_rat_grid%[[298162061103981312,19719832563658229880,63147319989610438080],[0,-96821053465823600,10119010976635680000],[1910703790510730352,193453928234470968280,477168885193568251680],[0,2480307834419869200,35325969321403980000],[5008715857670908320,671989036832940969000,1218502038995021998800],[0,2603797141560714000,43683281513159400000],[6831296250110229600,989784951511179357000,1385759874026499264000],[0,-1657953199209006000,22215064391674200000],[5059817569030913280,646842597904243512000,705835212309864115200],[0,-995370226582780800,3819350463271200000],[1894168762749179568,159707032207973313120,125877152599700721120],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
noncomputable def witness_62 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal015.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_17, 294400, by norm_num, R7.Core.Certificates.Terminal015.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_18, 1024, by norm_num, R7.Core.Certificates.Terminal015.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_19, 184320000, by norm_num, R7.Core.Certificates.Terminal015.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_20, 6635520000000, by norm_num, R7.Core.Certificates.Terminal015.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_21, 859963392000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_22, 4567941162152755200000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_22⟩
theorem bound_62 : minorBindings polynomial_62 witness_62 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_62 witness_62 (by decide +kernel)
theorem positive_62 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_62 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_62 ρ hρ u
noncomputable def polynomial_63 : BiPoly := r7_rat_grid%[[33419956126224384,1275800454489007160,4702290481602034560],[0,1476641418125122400,3372610242080880000],[316966705229179872,23644810331959628580,64217759878928283480],[0,8608494303413064600,18862747813211490000],[1232831119209863040,146711948491756000500,266689357078190673600],[0,10583402465604074400,37478541326828490000],[2490505240932146520,345676864663840541400,475613717184301906800],[0,-389887893308239200,30133805710703940000],[2726772547548944160,343043379158424084000,372503286463192214400],[0,-1922094230642611200,7375297446316800000],[1504876409668826712,126883807797132172080,100006694856817444080],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
noncomputable def witness_63 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_24, 18400, by norm_num, R7.Core.Certificates.Terminal015.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_25, 147200, by norm_num, R7.Core.Certificates.Terminal015.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_26, 384, by norm_num, R7.Core.Certificates.Terminal015.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_27, 13824000, by norm_num, R7.Core.Certificates.Terminal015.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_28, 41803776000000, by norm_num, R7.Core.Certificates.Terminal015.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_29, 18962192793600000000, by norm_num, R7.Core.Certificates.Terminal015.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_30, 117510286396379627520000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_30⟩
theorem bound_63 : minorBindings polynomial_63 witness_63 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_63 witness_63 (by decide +kernel)
theorem positive_63 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_63 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_63 ρ hρ u
noncomputable def polynomial_64 : BiPoly := r7_rat_grid%[[228519525948542208,9883384065634492420,34866778673220378720],[0,8889461922625517000,16400625736077900000],[2141672589264974112,170677545675271167180,452926316951338915080],[0,46214545662613243800,87585305313454470000],[8179725856475572560,998854833400263252000,1814893897893586655400],[0,52543282803156910800,165350653626452805000],[16194291487384426200,2270023857700630389000,3136306475826045558000],[0,-334616330824990200,124370229265255890000],[17328199737649741920,2188758435402988008000,2379660558651186652800],[0,-7207853364909792000,27657365423688000000],[9313964805788143704,785307891501169389360,618960354654356613360],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_64 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_0, 9200, by norm_num, R7.Core.Certificates.Terminal016.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_1, 73600, by norm_num, R7.Core.Certificates.Terminal016.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_2, 1152, by norm_num, R7.Core.Certificates.Terminal016.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_3, 207360000, by norm_num, R7.Core.Certificates.Terminal016.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_4, 39191040000000, by norm_num, R7.Core.Certificates.Terminal016.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_5, 17777055744000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_6, 660995360979635404800000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_6⟩
theorem bound_64 : minorBindings polynomial_64 witness_64 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_64 witness_64 (by decide +kernel)
theorem positive_64 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_64 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_64 ρ hρ u
noncomputable def polynomial_65 : BiPoly := r7_rat_grid%[[720221206391101440,35518030573115566225,121093004379226779600],[0,21408336864511411000,32947319065115700000],[6534426797408894040,560739122344518356850,1452616828853209676100],[0,97814363255323948200,159756178182735330000],[24142037588844245280,3036622748589873761625,5514120752436378700200],[0,100510729604604306000,270133261961485725000],[46094085627314124600,6532299153997076907000,9065617270358569501500],[0,3109117080228138000,178431685660812150000],[47410658165447771040,6013657737573414516000,6546539314816546953600],[0,-8649424037891750400,33188838508425600000],[24403401237872865600,2057575261575116304000,1621730186867309904000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_65 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal016.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_9, 230000, by norm_num, R7.Core.Certificates.Terminal016.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_10, 18000, by norm_num, R7.Core.Certificates.Terminal016.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_11, 1620000000, by norm_num, R7.Core.Certificates.Terminal016.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_12, 17146080000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_13, 666639590400000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_14, 61968315091840819200000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_14⟩
theorem bound_65 : minorBindings polynomial_65 witness_65 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_65 witness_65 (by decide +kernel)
theorem positive_65 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_65 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_65 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry010

namespace R7.Core.SpectralSliceCertificates.Entry011
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_66 : BiPoly := r7_rat_grid%[[1321231790009960640,73609230859089234850,243807053966685357600],[0,24347461246089070000,32253359436684000000],[11482186982967489960,1056948061757342684400,2679548008402673321400],[0,95745481455543385500,128551073847141825000],[40413914844538742640,5229265002151917156750,9489771362896442337600],[0,86124312530568216000,169049769394368600000],[73247630018455791000,10485708155183311380000,14611186141888248315000],[0,7506366154040155500,80916983614281150000],[71247927855311121600,9070423223173455780000,9885189891336397344000],[0,-1922094230642611200,7375297446316800000],[34571485086986559600,2914898287231414764000,2297451098062022364000],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
noncomputable def witness_66 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal016.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal016.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_18, 576000, by norm_num, R7.Core.Certificates.Terminal016.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_19, 518400000000, by norm_num, R7.Core.Certificates.Terminal016.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_20, 1102248000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_21, 24998984640000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_22, 3098415754592040960000000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_22⟩
theorem bound_66 : minorBindings polynomial_66 witness_66 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_66 witness_66 (by decide +kernel)
theorem positive_66 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_66 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_66 ρ hρ u
noncomputable def polynomial_67 : BiPoly := r7_rat_grid%[[1505186967817085760,92654460039862335525,300290033370024068400],[0,11098607873420455000,12744862315258500000],[12266223925677473880,1196147608012635639450,2981330790959545886700],[0,35475634872980974200,23888193824722230000],[40413914844538742640,5348121770409204368625,9700640657068843587600],[0,25810895890234638000,-6622150752143325000],[68295798440172370800,9851267008591191103500,13768402645003577359500],[0,6306037398428607000,-27958822609633650000],[61777524276189519840,7885426591980464436000,8600580904446637545600],[0,2883141345963916800,-11062946169475200000],[27860549746571521560,2349065090298257780400,1851475296673512140400],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_67 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_24, 34500, by norm_num, R7.Core.Certificates.Terminal016.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_25, 230000, by norm_num, R7.Core.Certificates.Terminal016.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_26, 6000, by norm_num, R7.Core.Certificates.Terminal016.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_27, 540000000, by norm_num, R7.Core.Certificates.Terminal016.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_28, 476280000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_29, 154314720000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_30, 14344517382370560000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_30⟩
theorem bound_67 : minorBindings polynomial_67 witness_67 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_67 witness_67 (by decide +kernel)
theorem positive_67 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_67 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_67 ρ hρ u
noncomputable def polynomial_68 : BiPoly := r7_rat_grid%[[1013485287374526528,67019813532381261720,214063807664017667520],[0,19892812775637800,-1561041862249140000],[7606205821832214744,768727681396232364660,1896479205395523141960],[0,-1117072575598679100,-16474625698857165000],[22883409342690563520,3066707797723814844000,5561027905188839716800],[0,-1995718852519812000,-34288940874394575000],[35272145210996286000,5108058781024727632500,7150351273336107990000],[0,1853516762133340500,-24680544117654600000],[29173534245281714400,3728682562669824060000,4068466319673490896000],[0,1441570672981958400,-5531473084737600000],[12079683612747068472,1018499754479682570480,802756442499318402480],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_68 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_0, 55200, by norm_num, R7.Core.Certificates.Terminal017.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_1, 294400, by norm_num, R7.Core.Certificates.Terminal017.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_2, 384, by norm_num, R7.Core.Certificates.Terminal017.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_3, 518400000, by norm_num, R7.Core.Certificates.Terminal017.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_4, 81648000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_5, 999959385600000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_6, 37180989055104491520000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_6⟩
theorem bound_68 : minorBindings polynomial_68 witness_68 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_68 witness_68 (by decide +kernel)
theorem positive_68 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_68 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_68 ρ hρ u
noncomputable def polynomial_69 : BiPoly := r7_rat_grid%[[337828429124842176,22339937844127087240,71354602554672555840],[0,0,0],[2173201663380632784,219636480398923532760,541851201541578040560],[0,0,0],[5720852335672640880,766676949430953711000,1390256976297209929200],[0,0,0],[7838254491332508000,1135124173561050585000,1588966949630246220000],[0,0,0],[5834706849056342880,745736512533964812000,813693263934698179200],[0,0,0],[2196306111408557904,185181773541760467360,145955716818057891360],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
noncomputable def witness_69 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_8, 18400, by norm_num, R7.Core.Certificates.Terminal017.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_9, 43276800, by norm_num, R7.Core.Certificates.Terminal017.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_10, 451584, by norm_num, R7.Core.Certificates.Terminal017.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_11, 406425600000, by norm_num, R7.Core.Certificates.Terminal017.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_12, 409677004800000000, by norm_num, R7.Core.Certificates.Terminal017.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_13, 10034792426373120000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_14, 62186443560964098883584000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_14⟩
theorem bound_69 : minorBindings polynomial_69 witness_69 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_69 witness_69 (by decide +kernel)
theorem positive_69 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_69 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_69 ρ hρ u
noncomputable def polynomial_70 : BiPoly := r7_rat_grid%[[36645616448534016,1730280772047848840,5931402065261221440],[0,1274153619500042800,1795084288524360000],[340220706736409856,28498032765540651840,74363724947015447040],[0,5825446500678300000,8856303392520000000],[1280352142527423840,159633996549998643000,289950236188289895600],[0,5940878687527053600,15118579898847810000],[2492221647025139040,352283789631173932800,488418664078039953600],[0,238584956885636400,9705374895184020000],[2613680598572259840,331322370836490216000,360614485503317145600],[0,-411877335137702400,1580420881353600000],[1371238736223332448,115616133745649392320,91125791452544080320],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
noncomputable def witness_70 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_16, 18400, by norm_num, R7.Core.Certificates.Terminal017.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_17, 588800, by norm_num, R7.Core.Certificates.Terminal017.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_18, 294912, by norm_num, R7.Core.Certificates.Terminal017.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_19, 10616832000, by norm_num, R7.Core.Certificates.Terminal017.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_20, 1146617856000000, by norm_num, R7.Core.Certificates.Terminal017.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_21, 297203348275200000000, by norm_num, R7.Core.Certificates.Terminal017.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_22, 1578680465639992197120000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_22⟩
theorem bound_70 : minorBindings polynomial_70 witness_70 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_70 witness_70 (by decide +kernel)
theorem positive_70 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_70 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_70 ρ hρ u
noncomputable def polynomial_71 : BiPoly := r7_rat_grid%[[223681035465077760,11634406198497624900,38893709105547098400],[0,6127307435322563000,3780313034318100000],[2016394274838636000,178128961518153700000,457017802851346740000],[0,23552475120716060400,14316413494469760000],[7388840254119024960,941331948383503789500,1708967138046188621400],[0,21051302409411570000,15200337953800125000],[13954381536029187600,1988096701514086692000,2765086695606008484000],[0,3538678089677499000,857049480864450000],[14149059394194060480,1798831022956828452000,1959602068348494163200],[0,892400892798355200,-3424245242932800000],[7146710362519910640,602575612318426917600,474935269011140757600],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_71 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal017.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal017.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal017.polynomial_25, 4508000000, by norm_num, R7.Core.Certificates.Terminal017.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal017.polynomial_26, 40000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal017.polynomial_27, 32400000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal017.polynomial_28, 1749600000000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal017.polynomial_29, 3401222400000000000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal017.polynomial_30, 90332820833587200000000000000000000000, by norm_num, R7.Core.Certificates.Terminal017.positive_30⟩
theorem bound_71 : minorBindings polynomial_71 witness_71 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_71 witness_71 (by decide +kernel)
theorem positive_71 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_71 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_71 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry011

namespace R7.Core.SpectralSliceCertificates.Entry012
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_72 : BiPoly := r7_rat_grid%[[600250438256019840,34381450245034896600,112666374919879185600],[0,10493417322793582000,-5308526263656600000],[5205963400492478400,486616010259238166000,1227692514376746306000],[0,31023350406244962600,-41690734370019810000],[18237211005756476160,2376569752230623907000,4312283982935053604400],[0,21573985421917296000,-99504836479969650000],[32817684498016982400,4712180863167347148000,6573990860741591316000],[0,11114654496658713000,-88167369190071600000],[31590351080820486720,4027062079261656828000,4390572844789955884800],[0,6555714250941763200,-25155032361544800000],[15106867432968916800,1273737066689357712000,1003928210917858512000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_72 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_0, 276000, by norm_num, R7.Core.Certificates.Terminal018.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_1, 73600000, by norm_num, R7.Core.Certificates.Terminal018.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_2, 128000000, by norm_num, R7.Core.Certificates.Terminal018.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_3, 92160000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_4, 1866240000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_5, 24186470400000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_6, 1284733451855462400000000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_6⟩
theorem bound_72 : minorBindings polynomial_72 witness_72 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_72 witness_72 (by decide +kernel)
theorem positive_72 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_72 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_72 ρ hρ u
noncomputable def polynomial_73 : BiPoly := r7_rat_grid%[[897103727343982080,55787354436120314200,180356449929270187200],[0,6563884044685430000,-24569973170334000000],[7302489707551974480,716864600654915572200,1783592495397972628200],[0,8272275895314609300,-133521399891929205000],[23998116775368204000,3186645224606880360000,5779577195389615860000],[0,-1517914313661672000,-238349420995234950000],[40352707246254145200,5829443193456634824000,8152061911266379518000],[0,14249427428094043500,-165526732850287950000],[36214555216756023360,4625714690546728284000,5046292401779635142400],[0,9782086709520432000,-37534995932148000000],[16152727486020611040,1361918863614005553600,1073430933212171793600],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_73 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_8, 92000, by norm_num, R7.Core.Certificates.Terminal018.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_9, 7360000, by norm_num, R7.Core.Certificates.Terminal018.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_10, 384000, by norm_num, R7.Core.Certificates.Terminal018.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_11, 138240000000, by norm_num, R7.Core.Certificates.Terminal018.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_12, 466560000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_13, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_14, 32118336296386560000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_14⟩
theorem bound_73 : minorBindings polynomial_73 witness_73 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_73 witness_73 (by decide +kernel)
theorem positive_73 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_73 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_73 ρ hρ u
noncomputable def polynomial_74 : BiPoly := r7_rat_grid%[[745405152759953280,49299581409145574700,157868299974026095200],[0,270570347621833000,-28795991067657900000],[5600862435097239840,567270508621186622600,1399165497406699860600],[0,-8804158762080797700,-124829251586758755000],[16818369023846446560,2257273716317280649500,4093002199180389065400],[0,-11023266855283758000,-184127466691402425000],[25814747638607500800,3741130972969910586000,5238228882700376622000],[0,8094202433120695500,-108609842232390600000],[21219400500588250560,2713003861309653204000,2960542352144720390400],[0,5526020913097507200,-21203980158160800000],[8715500442097452000,734848307705398680000,579189352452610680000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_74 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_16, 138000, by norm_num, R7.Core.Certificates.Terminal018.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_17, 3680000, by norm_num, R7.Core.Certificates.Terminal018.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_18, 128000, by norm_num, R7.Core.Certificates.Terminal018.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_19, 46080000000, by norm_num, R7.Core.Certificates.Terminal018.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_20, 51840000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_21, 5038848000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_22, 133826401234944000000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_22⟩
theorem bound_74 : minorBindings polynomial_74 witness_74 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_74 witness_74 (by decide +kernel)
theorem positive_74 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_74 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_74 ρ hρ u
noncomputable def polynomial_75 : BiPoly := r7_rat_grid%[[33016748585935680,1827176067094500700,6016300985598511200],[0,735480846643114000,-176849421748200000],[291460626999402840,26720969901075517600,67777122620952030600],[0,2247214717255077600,-1956086246707560000],[1046989974450116340,135561739252126795500,246022886893865970600],[0,1549776422648484000,-5649027948329850000],[1930956854616585000,276846806859037965000,386010008852727150000],[0,735553924365852000,-5851596939273900000],[1903714474440852720,242631273966400728000,264516463647550324800],[0,480523557660652800,-1843824361579200000],[929653380490394880,78383819488575859200,61780197594945139200],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
noncomputable def witness_75 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal018.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_25, 3680000, by norm_num, R7.Core.Certificates.Terminal018.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal018.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_27, 576000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_28, 373248000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_29, 3869835264000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_30, 12847334518554624000000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_30⟩
theorem bound_75 : minorBindings polynomial_75 witness_75 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_75 witness_75 (by decide +kernel)
theorem positive_75 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_75 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_75 ρ hρ u
noncomputable def polynomial_76 : BiPoly := r7_rat_grid%[[170437810267938240,10070507951939492600,32806284299305341600],[0,2525636116463600000,-6410228632042500000],[1463195196189724500,139704676206183942500,350353394585108955000],[0,4613395316271041100,-35944655630005035000],[5054200265703430800,665214459938190915000,1206741630330888147000],[0,984545658464733000,-69336322781381325000],[8933893714026066600,1287935457999236194500,1799593079761359594000],[0,4640790330914629500,-52269146602293150000],[8406501540600201120,1073385863554069863000,1170853523932126780800],[0,3303599458916988000,-12676292485857000000],[3907449364873690980,329456991287920408200,259669893016253788200],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_76 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_0, 92000, by norm_num, R7.Core.Certificates.Terminal019.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_1, 92000000, by norm_num, R7.Core.Certificates.Terminal019.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_2, 250000000, by norm_num, R7.Core.Certificates.Terminal019.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_3, 22500000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_4, 20958750000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_5, 147622500000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_6, 1960347674340000000000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_6⟩
theorem bound_76 : minorBindings polynomial_76 witness_76 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_76 witness_76 (by decide +kernel)
theorem positive_76 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_76 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_76 ρ hρ u
noncomputable def polynomial_77 : BiPoly := r7_rat_grid%[[374115455260906320,23548502722294089300,76270770269481268800],[0,2367519282687384000,-22437996767674200000],[3017913742906215660,299555445745798074900,743464561810906634400],[0,-2518595367126786000,-110336430391155900000],[9810375828029587440,1310239447510166673000,2375957306668762119600],[0,-7666798906621710000,-182356837473534750000],[16254365700639164400,2353877412604168810500,3294721740750725196000],[0,9212238672807114000,-118223093834997300000],[14309272988577696600,1829635359849620257500,1996615161319871844000],[0,6487068028418812800,-24891628881319200000],[6231582816099678180,525416540009360056200,414120387003616636200],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
noncomputable def witness_77 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_8, 138000, by norm_num, R7.Core.Certificates.Terminal019.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_9, 49680000, by norm_num, R7.Core.Certificates.Terminal019.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_10, 1296000, by norm_num, R7.Core.Certificates.Terminal019.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_11, 349920000000, by norm_num, R7.Core.Certificates.Terminal019.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_12, 94478400000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_13, 45916502400000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_14, 914619810940070400000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_14⟩
theorem bound_77 : minorBindings polynomial_77 witness_77 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_77 witness_77 (by decide +kernel)
theorem positive_77 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_77 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_77 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry012

namespace R7.Core.SpectralSliceCertificates.Entry013
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_78 : BiPoly := r7_rat_grid%[[407355289985936160,26955989540709193400,86928971940351854400],[0,107481204180206000,-29997208943655300000],[3044624420313169020,310119152354110445300,764394353025989536800],[0,-9378852821169054900,-124544488589637435000],[9052076070233652960,1219270104993796257000,2210543280144209516400],[0,-11078658750357225000,-176562306709363125000],[13705502652545272200,1989413391549046936500,2787112893174405948000],[0,7368188996151301500,-100127809940903550000],[11076728113660803120,1417229125570704573000,1546873549954677460800],[0,4882462576944847200,-18734572531045800000],[4459431059539862940,375997384109262324600,296351885338252464600],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_78 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_16, 92000, by norm_num, R7.Core.Certificates.Terminal019.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_17, 3680000, by norm_num, R7.Core.Certificates.Terminal019.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal019.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_19, 1440000000, by norm_num, R7.Core.Certificates.Terminal019.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_20, 19440000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_21, 3149280000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_22, 41820750385920000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_22⟩
theorem bound_78 : minorBindings polynomial_78 witness_78 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_78 witness_78 (by decide +kernel)
theorem positive_78 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_78 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_78 ρ hρ u
noncomputable def polynomial_79 : BiPoly := r7_rat_grid%[[23200958465792640,1425812403944553600,4616373850690737600],[0,234372094039416000,-1345895508565800000],[195616431597981960,19169496978673979400,47733144298489976400],[0,26436862613530200,-7118329585908870000],[657826737067377360,87575773651986072000,158821301454034712400],[0,-470001597073830000,-12897392641049250000],[1127106667731754800,163164854284702281000,228349569345756732000],[0,704373884929539000,-9014656160832300000],[1022016131492999040,130694070138059646000,142626799252672473600],[0,520567187465707200,-1997476391710800000],[455142800865089160,38375411624615264400,30246555072525224400],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
noncomputable def witness_79 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_24, 2208000, by norm_num, R7.Core.Certificates.Terminal019.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_25, 1589760000, by norm_num, R7.Core.Certificates.Terminal019.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_26, 3456000, by norm_num, R7.Core.Certificates.Terminal019.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_27, 622080000000, by norm_num, R7.Core.Certificates.Terminal019.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_28, 5598720000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_29, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_30, 892176008232960000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_30⟩
theorem bound_79 : minorBindings polynomial_79 witness_79 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_79 witness_79 (by decide +kernel)
theorem positive_79 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_79 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_79 ρ hρ u
noncomputable def polynomial_80 : BiPoly := r7_rat_grid%[[99050245757807040,6343732302392132100,20601224537617533600],[0,402744528179586000,-8547366966999300000],[784822550869011960,79055588562374084400,195562190369831801400],[0,-2302948023375755700,-40149702367028955000],[2498926954742018640,336162900940575790500,609457391053045302600],[0,-3629631370536621000,-63031705074522225000],[4033554318532422000,585749869700004945000,820725388032910230000],[0,2861611599131077500,-38566193224416750000],[3438832967031771360,440174231761855014000,480501891101297462400],[0,1982159675350192800,-7605775491514200000],[1442899517636133720,121658219831227114800,95888015017154434800],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_80 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_0, 414000, by norm_num, R7.Core.Certificates.Terminal020.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_1, 298080000, by norm_num, R7.Core.Certificates.Terminal020.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_2, 279936000, by norm_num, R7.Core.Certificates.Terminal020.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_3, 83980800000000, by norm_num, R7.Core.Certificates.Terminal020.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_4, 188956800000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_5, 20407334400000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_6, 90332820833587200000000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_6⟩
theorem bound_80 : minorBindings polynomial_80 witness_80 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_80 witness_80 (by decide +kernel)
theorem positive_80 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_80 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_80 ρ hρ u
noncomputable def polynomial_81 : BiPoly := r7_rat_grid%[[157944986478665280,10476322483509074700,34105430508708175200],[0,-86970003452298000,-16461270244475100000],[1166628116156639400,119842948083641166000,295039062780293421000],[0,-5422711845072293100,-65922097598523765000],[3403184141299032720,460669760897906191500,835047165091281319800],[0,-5983103806325415000,-89729885854105875000],[5029069852468083600,731501833829827167000,1025578582234352874000],[0,3522706379980906500,-48646097123939550000],[3949841032778270880,505798782956683902000,552209504895937699200],[0,2256744565441994400,-8659389412416600000],[1539738411437216520,129823201027953766800,102323452266627886800],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_81 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_8, 414000, by norm_num, R7.Core.Certificates.Terminal020.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_9, 1490400000, by norm_num, R7.Core.Certificates.Terminal020.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_10, 11664000000, by norm_num, R7.Core.Certificates.Terminal020.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_11, 2099520000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_12, 4723920000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_13, 1530550080000000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_14, 6774961562519040000000000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_14⟩
theorem bound_81 : minorBindings polynomial_81 witness_81 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_81 witness_81 (by decide +kernel)
theorem positive_81 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_81 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_81 ρ hρ u
noncomputable def polynomial_82 : BiPoly := r7_rat_grid%[[12849761611823616,841002739295060340,2735332752316285440],[0,10237277424092400,-1305704740830120000],[98279580694407804,10060268618872623060,24792494784419367360],[0,-468520663459210200,-5894441597633130000],[302437369828190520,40959848092519336500,74245087774398646800],[0,-584925794985175200,-8737123222589670000],[468578863386957960,68200517654590304700,95640206802855026400],[0,361010154347353800,-5008841796633660000],[381161753958454560,48826625310953109000,53312338444457750400],[0,240261778830326400,-921912180789600000],[152037063267699996,12819020478860843640,10103636481673319640],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
noncomputable def witness_82 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_16, 82800, by norm_num, R7.Core.Certificates.Terminal020.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_17, 5961600, by norm_num, R7.Core.Certificates.Terminal020.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_18, 93312, by norm_num, R7.Core.Certificates.Terminal020.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_19, 5038848000, by norm_num, R7.Core.Certificates.Terminal020.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_20, 90699264000000, by norm_num, R7.Core.Certificates.Terminal020.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_21, 979552051200000000, by norm_num, R7.Core.Certificates.Terminal020.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_22, 433597540001218560000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_22⟩
theorem bound_82 : minorBindings polynomial_82 witness_82 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_82 witness_82 (by decide +kernel)
theorem positive_82 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_82 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_82 ρ hρ u
noncomputable def polynomial_83 : BiPoly := r7_rat_grid%[[39352394936209824,2622601796563945260,8614589314108124160],[0,-80317143973162800,-5022571827618360000],[284940079279470108,29561394130381153620,72651029719225014720],[0,-1725306591572173800,-19202659477171470000],[806499652875174720,109718311168816726500,198851104148098474800],[0,-1748731466980180800,-24775432065785430000],[1148275676211995880,167333991358628159100,234765301820199559200],[0,905466456495912600,-12689275730323320000],[864943980136493040,110838017402852436000,121033593083594433600],[0,554890298727182400,-2129178131823600000],[322473516357605724,27189387385099751160,21430006040746595160],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
noncomputable def witness_83 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_24, 82800, by norm_num, R7.Core.Certificates.Terminal020.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_25, 5961600, by norm_num, R7.Core.Certificates.Terminal020.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_26, 93312, by norm_num, R7.Core.Certificates.Terminal020.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_27, 5038848000, by norm_num, R7.Core.Certificates.Terminal020.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_28, 90699264000000, by norm_num, R7.Core.Certificates.Terminal020.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_29, 8815968460800000000, by norm_num, R7.Core.Certificates.Terminal020.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_30, 7804755720021934080000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_30⟩
theorem bound_83 : minorBindings polynomial_83 witness_83 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_83 witness_83 (by decide +kernel)
theorem positive_83 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_83 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_83 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry013

namespace R7.Core.SpectralSliceCertificates.Entry014
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_84 : BiPoly := r7_rat_grid%[[4818660604433856,323927101321615440,1068955738507607040],[0,-16464440254046400,-675794015779680000],[33938272470011328,3545659183910641920,8701551806328299520],[0,-228506532384175200,-2419675978097880000],[91647687826724400,12501538741144980000,22655639340672696000],[0,-211601031271819200,-2916056153308320000],[123581238695461440,18024267946188700800,25295471821335369600],[0,98992054936101600,-1396442533398120000],[87960404759643360,11274798562163514000,12312955388933942400],[0,57205185435792000,-219502900188000000],[30988446016346496,2612793982952528640,2059339919831504640],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
noncomputable def witness_84 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_0, 8942400, by norm_num, R7.Core.Certificates.Terminal021.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_1, 1514341785600, by norm_num, R7.Core.Certificates.Terminal021.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_2, 139314069504, by norm_num, R7.Core.Certificates.Terminal021.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_3, 361102068154368000, by norm_num, R7.Core.Certificates.Terminal021.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_4, 19499511680335872000000, by norm_num, R7.Core.Certificates.Terminal021.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_5, 6739031236724077363200000000, by norm_num, R7.Core.Certificates.Terminal021.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_6, 542368016381532504714117120000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_6⟩
theorem bound_84 : minorBindings polynomial_84 witness_84 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_84 witness_84 (by decide +kernel)
theorem positive_84 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_84 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_84 ρ hρ u
noncomputable def polynomial_85 : BiPoly := r7_rat_grid%[[317278064489472,-2126945970126720,8582142896772480],[0,5416157092356000,105138593287200000],[3770919163334592,105844395827756880,451714058526158280],[0,229955636259896400,730710772395660000],[16292922280306560,1469402662266792000,2671618533500840400],[0,449649281386999800,1693614323077830000],[34328121859850400,4323051783673015500,5675183447198436000],[0,-11411149897095300,1543482320988960000],[37697316325561440,4554540400842441000,4882766712667689600],[0,-111550111599794400,428030655366600000],[20336167698227388,1714646051312596920,1351441822389424920],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
noncomputable def witness_85 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_8, 2649600, by norm_num, R7.Core.Certificates.Terminal021.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_9, 572313600, by norm_num, R7.Core.Certificates.Terminal021.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_10, 6718464, by norm_num, R7.Core.Certificates.Terminal021.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_11, 1813985280000, by norm_num, R7.Core.Certificates.Terminal021.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_12, 1689727288320000000, by norm_num, R7.Core.Certificates.Terminal021.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_13, 2380311484416000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_14, 191571276764174745600000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_14⟩
theorem bound_85 : minorBindings polynomial_85 witness_85 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_85 witness_85 (by decide +kernel)
theorem positive_85 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_85 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_85 ρ hρ u
noncomputable def polynomial_86 : BiPoly := r7_rat_grid%[[3014141612649984,-9600963989713840,110799436055338560],[0,66473440976713600,945896234332320000],[35195245524456192,1080104662396270880,4383368501480477280],[0,2121839437821974400,6669716100381360000],[154782761662912320,14142814452164026500,25716045985634233800],[0,4232533028320479600,15957755353844910000],[336415594226533920,42500265119721779400,55886303473642297800],[0,-115152546330271800,15114355005736260000],[383256049309874640,46350746762864661000,49707163940172177600],[0,-1138383190172260800,4368107713741200000],[214982344238403816,18126258256733167440,14286670693831063440],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
noncomputable def witness_86 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_16, 36800, by norm_num, R7.Core.Certificates.Terminal021.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_17, 2355200, by norm_num, R7.Core.Certificates.Terminal021.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_18, 65536, by norm_num, R7.Core.Certificates.Terminal021.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_19, 2359296000, by norm_num, R7.Core.Certificates.Terminal021.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_20, 63700992000000, by norm_num, R7.Core.Certificates.Terminal021.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_21, 4127824281600000000, by norm_num, R7.Core.Certificates.Terminal021.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_22, 3654352929722204160000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_22⟩
theorem bound_86 : minorBindings polynomial_86 witness_86 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_86 witness_86 (by decide +kernel)
theorem positive_86 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_86 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_86 ρ hρ u
noncomputable def polynomial_87 : BiPoly := r7_rat_grid%[[14277512902026240,17836086054365100,741973101721761600],[0,445457386858783000,4185847663644600000],[164453974623203040,5958986327290383100,22179913819058861100],[0,9529967617513208100,29232029383918515000],[723677297950283040,68485494048159143625,124546691165013161100],[0,18529587619587567000,70229317543642575000],[1587675636018081000,202667242700569792500,267936438299112540000],[0,-578424071584800000,67398048057678750000],[1836697023195410160,222971141345497569000,239410399145696654400],[0,-5179929541210965600,19875987612023400000],[1050701997741748380,88590045984484174200,69824494156786954200],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_87 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_24, 414000, by norm_num, R7.Core.Certificates.Terminal021.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_25, 1840000, by norm_num, R7.Core.Certificates.Terminal021.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal021.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_27, 21600000000, by norm_num, R7.Core.Certificates.Terminal021.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_28, 777600000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_29, 41990400000000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_30, 185870001715200000000000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_30⟩
theorem bound_87 : minorBindings polynomial_87 witness_87 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_87 witness_87 (by decide +kernel)
theorem positive_87 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_87 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_87 ρ hρ u
noncomputable def polynomial_88 : BiPoly := r7_rat_grid%[[44022331447914240,289572006163642600,3136987401429681600],[0,1765810758988294000,11928841936192800000],[497551834051092000,21694831106613675000,74045319912264780000],[0,27120038452283260200,81270596640015630000],[2168995278565810800,215645917730427862500,392191378672572972000],[0,49810235164190244000,191759907968109900000],[4737280816659355200,614670757889978124000,819316496263793418000],[0,-1950922532218401000,181775469690088200000],[5474488048612089120,668913413607804798000,719730015150504700800],[0,-13900860060897456000,53339204745684000000],[3137580159155082720,264545390773943524800,208508166882939844800],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_88 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_0, 92000, by norm_num, R7.Core.Certificates.Terminal022.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_1, 184000000, by norm_num, R7.Core.Certificates.Terminal022.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_2, 6000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_3, 2160000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_4, 9720000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_5, 7822811520000000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_6, 103882743958625280000000000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_6⟩
theorem bound_88 : minorBindings polynomial_88 witness_88 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_88 witness_88 (by decide +kernel)
theorem positive_88 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_88 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_88 ρ hρ u
noncomputable def polynomial_89 : BiPoly := r7_rat_grid%[[97265556645053760,1264779696740186775,9082228384839938400],[0,4456994742202503000,24233911495946100000],[1074319157470844700,56189499920441790500,177490767123798273000],[0,53217262712705181300,158903721053432595000],[4598677313616526560,483962185178509116375,880029519042266577900],[0,90657020577385665000,361573394230949625000],[9886499095636915200,1309082783402112196500,1762086677856459318000],[0,-4826366001651852000,330844296459911400000],[11258931809234350080,1387485980046584082000,1496952646677208627200],[0,-24523862996324030400,94100893310595600000],[6362315322731139960,536439264624941036400,422808227290405796400],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_89 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_8, 34500, by norm_num, R7.Core.Certificates.Terminal022.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_9, 6900000, by norm_num, R7.Core.Certificates.Terminal022.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal022.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_11, 180000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_12, 38880000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_13, 37791360000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_14, 1003698009262080000000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_14⟩
theorem bound_89 : minorBindings polynomial_89 witness_89 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_89 witness_89 (by decide +kernel)
theorem positive_89 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_89 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_89 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry014

namespace R7.Core.SpectralSliceCertificates.Entry015
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_90 : BiPoly := r7_rat_grid%[[161246661337258848,3342181498941889770,18903577511702776320],[0,7526661097184738000,36807370188015600000],[1730066287811549688,107180933230524954820,316664490428264851920],[0,74246684102306193600,229405094331612840000],[7212333596082370560,805255361533772828250,1463644768185555350400],[0,115941379502345216400,494855583135119190000],[15104373618334176000,2044717846874946945000,2780541506428049340000],[0,-8845951833463361400,428016863197473480000],[16741797039252119520,2082942997316978958000,2254035424581163036800],[0,-30032722353790800000,115239022598700000000],[9191947799598779376,775020015193293807840,610851703720020063840],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_90 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_16, 13800, by norm_num, R7.Core.Certificates.Terminal022.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_17, 36800, by norm_num, R7.Core.Certificates.Terminal022.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_18, 128, by norm_num, R7.Core.Certificates.Terminal022.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_19, 345600000, by norm_num, R7.Core.Certificates.Terminal022.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_20, 21772800000000, by norm_num, R7.Core.Certificates.Terminal022.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_21, 19752284160000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_22, 734439289977372672000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_22⟩
theorem bound_90 : minorBindings polynomial_90 witness_90 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_90 witness_90 (by decide +kernel)
theorem positive_90 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_90 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_90 ρ hρ u
noncomputable def polynomial_91 : BiPoly := r7_rat_grid%[[204257668954612896,6089562143346601290,28974677585873120640],[0,8636877775518875400,42688720956039480000],[2116192697973831348,152641530828410387220,426031323435346238820],[0,73866841361491602900,249861351341578635000],[8517125122030254240,1006877968710270792375,1828939008289487444100],[0,104890026193084099800,502901246803434705000],[17194956239599065360,2379333818912200292700,3267115238176842092400],[0,-11838744173407397400,403371830052756180000],[18325084324925700000,2301430274480669850000,2497744615006998000000],[0,-26308664781920740800,100949383796461200000],[9639343488959781912,812742228322170940080,640583423812587412080],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_91 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_24, 96600, by norm_num, R7.Core.Certificates.Terminal022.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_25, 373262400, by norm_num, R7.Core.Certificates.Terminal022.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_26, 556416, by norm_num, R7.Core.Certificates.Terminal022.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_27, 10015488000, by norm_num, R7.Core.Certificates.Terminal022.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_28, 31548787200000000, by norm_num, R7.Core.Certificates.Terminal022.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_29, 42931589621760000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_30, 1596303796765819502592000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_30⟩
theorem bound_91 : minorBindings polynomial_91 witness_91 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_91 witness_91 (by decide +kernel)
theorem positive_91 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_91 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_91 ρ hρ u
noncomputable def polynomial_92 : BiPoly := r7_rat_grid%[[198100491515614080,7914520551616339200,32894972689080067200],[0,6620773558335996000,37921901343955200000],[1965591613888156080,161797983795075841200,430614940267489597200],[0,51476991144719512200,206049236957669430000],[7563989168632320480,941636351662011336000,1709136105393574843200],[0,66222137665634256000,381460369241352600000],[14555123668576569600,2054469751954570782000,2845010614772788614000],[0,-11327753923982487000,279362370081668400000],[14727084911186002560,1864782083341892304000,2028952159586476070400],[0,-16749678295599897600,64270449175046400000],[7321020371361859680,617272578472534891200,486519056060192971200],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_92 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_0, 4416000, by norm_num, R7.Core.Certificates.Terminal023.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_1, 529920000, by norm_num, R7.Core.Certificates.Terminal023.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_2, 82944000, by norm_num, R7.Core.Certificates.Terminal023.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_3, 29859840000000, by norm_num, R7.Core.Certificates.Terminal023.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_4, 403107840000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_5, 4701849845760000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_6, 124876091520350945280000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_6⟩
theorem bound_92 : minorBindings polynomial_92 witness_92 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_92 witness_92 (by decide +kernel)
theorem positive_92 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_92 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_92 ρ hρ u
noncomputable def polynomial_93 : BiPoly := r7_rat_grid%[[144559818133015680,7303382826041310075,27281254876810711200],[0,3179271758704623000,25417447076690100000],[1361066135516079300,124929625694496979500,320080284516873762000],[0,24254859246831747900,126890358850010385000],[4948975142643117600,643252258592074175625,1166701222984985896500],[0,28419799689002700000,213648325251935625000],[8959639805420954400,1285242662172770568000,1791700602603956046000],[0,-7519306191027529500,141556351176779400000],[8490273354657004320,1081841967690036453000,1179338831617119868800],[0,-7765603922908764000,29797518700521000000],[3936501033014015820,331906485646938403800,261600524191095823800],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_93 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_8, 931500, by norm_num, R7.Core.Certificates.Terminal023.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_9, 5030100000, by norm_num, R7.Core.Certificates.Terminal023.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_10, 39366000000, by norm_num, R7.Core.Certificates.Terminal023.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_11, 14171760000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_12, 15943230000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_13, 2582803260000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_14, 34298242910252640000000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_14⟩
theorem bound_93 : minorBindings polynomial_93 witness_93 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_93 witness_93 (by decide +kernel)
theorem positive_93 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_93 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_93 ρ hρ u
noncomputable def polynomial_94 : BiPoly := r7_rat_grid%[[76295459570202720,4592305723457321550,15861262020055444800],[0,826301427549516000,12361656618529200000],[671694975968974200,66907948786381840500,166752877815222678000],[0,7447245998879703600,56136664245719340000],[2272862658102765120,304876404008002842750,552664725690087235800],[0,8148868503653268000,85430565475507800000],[3810421526443394400,552713846248702728000,773989456172309271000],[0,-3286429630415694000,51052542414153300000],[3332023904109347280,426298394185838037000,465287635826341675200],[0,-2557071788979902400,9811779638403600000],[1423531738875917160,120025223591881784400,94600927567259744400],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_94 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_16, 207000, by norm_num, R7.Core.Certificates.Terminal023.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_17, 1117800000, by norm_num, R7.Core.Certificates.Terminal023.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_18, 1458000000, by norm_num, R7.Core.Certificates.Terminal023.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_19, 262440000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_20, 9447840000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_21, 3061100160000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_22, 13549923125038080000000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_22⟩
theorem bound_94 : minorBindings polynomial_94 witness_94 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_94 witness_94 (by decide +kernel)
theorem positive_94 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_94 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_94 ρ hρ u
noncomputable def polynomial_95 : BiPoly := r7_rat_grid%[[26502633324386208,1781599057268884920,5879256561791838720],[0,97022594354202000,3982357592987400000],[214235344966946508,22381973598435927120,54928545777447390720],[0,1542419093593182600,16332812852160690000],[659863352352415680,90011078936243856000,163120603252843411200],[0,1620671534968251600,22334339174202360000],[1004097564400624200,146447177062783194000,205525708548349878000],[0,-850950933777642600,12004034854403070000],[797926528891050480,102278529813911877000,111696095313900763200],[0,-546309520911813600,2096252696795400000],[310852849101475788,26209589641492552920,20657753570809780920],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
noncomputable def witness_95 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_24, 49183200, by norm_num, R7.Core.Certificates.Terminal023.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_25, 31870713600, by norm_num, R7.Core.Certificates.Terminal023.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_26, 68024448, by norm_num, R7.Core.Certificates.Terminal023.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_27, 330598817280000, by norm_num, R7.Core.Certificates.Terminal023.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_28, 8926168066560000000, by norm_num, R7.Core.Certificates.Terminal023.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_29, 289207845356544000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_30, 256035011395319547494400000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_30⟩
theorem bound_95 : minorBindings polynomial_95 witness_95 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_95 witness_95 (by decide +kernel)
theorem positive_95 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_95 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_95 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry015

namespace R7.Core.SpectralSliceCertificates.Entry016
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_96 : BiPoly := r7_rat_grid%[[2538224515915776,4194477691966240,127195300246179840],[0,73369153937511200,735267942505440000],[28910380252231872,995920970687216080,3797882359173213480],[0,1714166876785088400,5301613704410460000],[130343378242452480,12122199619393341000,22044288102759223200],[0,3518923961383961400,13285753153833690000],[295221847994713440,37446960619040388300,49345589028101799600],[0,-104782443792495300,13250404480593960000],[351841619038573440,42601549116462471000,45703894040999769600],[0,-1049715152746783200,4027878218449800000],[206266843796306364,17391409949027768760,13707481341378452760],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
noncomputable def witness_96 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_0, 73600, by norm_num, R7.Core.Certificates.Terminal024.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_1, 1177600, by norm_num, R7.Core.Certificates.Terminal024.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_2, 1024, by norm_num, R7.Core.Certificates.Terminal024.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_3, 18432000, by norm_num, R7.Core.Certificates.Terminal024.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_4, 248832000000, by norm_num, R7.Core.Certificates.Terminal024.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_5, 8062156800000000, by norm_num, R7.Core.Certificates.Terminal024.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_6, 7137408065863680000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_6⟩
theorem bound_96 : minorBindings polynomial_96 witness_96 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_96 witness_96 (by decide +kernel)
theorem positive_96 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_96 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_96 ρ hρ u
noncomputable def polynomial_97 : BiPoly := r7_rat_grid%[[23002659675486720,110921985328062800,1353932323416004800],[0,815198250589052000,6351229499432400000],[263964341433421440,10175816748059181600,36641102753921079600],[0,15150162844398410400,45779452521809760000],[1197529787602532160,114423216298641799500,208112409320480519400],[0,30569943366723042000,115735743692002575000],[2746249748788032000,351218448282890340000,464794903419779880000],[0,-1014192254024149500,117576098607544650000],[3336212494812187440,405158196418049016000,435081460333370529600],[0,-9564707004864422400,36700884911433600000],[2004565101682413960,169015110772241696400,133213551064100456400],[0,0,0],[448932439011941280,-1891153445141188800,2254563784377115200]]
noncomputable def witness_97 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_8, 184000, by norm_num, R7.Core.Certificates.Terminal024.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_9, 29440000, by norm_num, R7.Core.Certificates.Terminal024.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_10, 3072000, by norm_num, R7.Core.Certificates.Terminal024.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_11, 5529600000000, by norm_num, R7.Core.Certificates.Terminal024.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_12, 167961600000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_13, 163258675200000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_14, 1445325133337395200000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_14⟩
theorem bound_97 : minorBindings polynomial_97 witness_97 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_97 witness_97 (by decide +kernel)
theorem positive_97 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_97 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_97 ρ hρ u
noncomputable def polynomial_98 : BiPoly := r7_rat_grid%[[103908566120302080,1015069519982256700,7781760206395987200],[0,4389980417363637000,26565382233959400000],[1180507193632801440,53187522473673369100,178208451325754342100],[0,63760195843375494300,188059290036471045000],[5319639124520091840,531054800896386143625,965933841781561890600],[0,122322381708919176000,468602146689131475000],[12160737168852004200,1578230672292016209000,2104062427940145453000],[0,-4923896554999093500,472272539553529200000],[14787819476377184880,1806302379485682432000,1943324379040786459200],[0,-38459046168482961600,147571799796392400000],[8933387953149888300,753219515398033647000,593669086263925947000],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
noncomputable def witness_98 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal024.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal024.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal024.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_19, 8640000000, by norm_num, R7.Core.Certificates.Terminal024.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_20, 19440000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_21, 47239200000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_22, 1881933767366400000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_22⟩
theorem bound_98 : minorBindings polynomial_98 witness_98 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_98 witness_98 (by decide +kernel)
theorem positive_98 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_98 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_98 ρ hρ u
noncomputable def polynomial_99 : BiPoly := r7_rat_grid%[[301017563684386560,4754281717097516900,28539847539347390400],[0,14049635267005093000,70602788615804100000],[3362402920640011200,178670735549077120500,558493360877214445500],[0,164978626659957063300,483357787830095895000],[14905987271195464080,1569463003613881967250,2854230030649945267200],[0,294947064446496048000,1164659974377839550000],[33572903178933691200,4441557879506354859000,5976573381415894158000],[0,-15755299584852168000,1136553619896327600000],[40285865379916658880,4960715937385973832000,5350768796933217619200],[0,-90132490172633875200,345848769536212800000],[24054781220188967520,2028181329266900356800,1598562612769205476800],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
noncomputable def witness_99 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal024.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal024.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_26, 6000000, by norm_num, R7.Core.Certificates.Terminal024.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_27, 1080000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_28, 933120000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_29, 10883911680000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_30, 1156260106669916160000000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_30⟩
theorem bound_99 : minorBindings polynomial_99 witness_99 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_99 witness_99 (by decide +kernel)
theorem positive_99 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_99 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_99 ρ hρ u
noncomputable def polynomial_100 : BiPoly := r7_rat_grid%[[616312640270799360,14187689523640518275,72214923452899292400],[0,28784006023349590000,131723434754320500000],[6713938261746801180,418305878049549117700,1228830075765174593700],[0,285014397170579888400,860449718333780460000],[29029914272936213280,3235533259742050875375,5881684161040896445200],[0,468894424712528619000,1969883716435744275000],[63747322293742192800,8616836333253310213500,11710784684023839027000],[0,-35569521491377072500,1821140493772257000000],[74531782966337807040,9263847483255837906000,10021705544329163193600],[0,-137069344822701211200,525950899140466800000],[43316037197224336440,3652196089295831439600,2878571081689475079600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_100 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_0, 11500, by norm_num, R7.Core.Certificates.Terminal025.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_1, 1380000, by norm_num, R7.Core.Certificates.Terminal025.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal025.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_3, 1440000000, by norm_num, R7.Core.Certificates.Terminal025.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_4, 45360000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_5, 308629440000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_6, 57378069529482240000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_6⟩
theorem bound_100 : minorBindings polynomial_100 witness_100 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_100 witness_100 (by decide +kernel)
theorem positive_100 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_100 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_100 ρ hρ u
noncomputable def polynomial_101 : BiPoly := r7_rat_grid%[[928127573087343264,29242889922407080860,130605245633298533760],[0,38787976888322923800,180405849684729060000],[9793548432075352248,706029824682570510720,1965304949374652557320],[0,337076609571458831700,1109992125309323355000],[40938003844555270320,4825155710433379246500,8765745082180542703800],[0,506037216139141579200,2375049681100916820000],[86740298315469990720,11981954446312496720400,16441473222973514584800],[0,-56969089701730970400,2038850392546929780000],[97606729148284248480,12246641094302159832000,13287371052988706083200],[0,-142715496625213881600,547615835389022400000],[54419584760456490288,4588392833312509357920,3616458316714101085920],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
noncomputable def witness_101 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_8, 82800, by norm_num, R7.Core.Certificates.Terminal025.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_9, 584236800, by norm_num, R7.Core.Certificates.Terminal025.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_10, 248832, by norm_num, R7.Core.Certificates.Terminal025.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_11, 53747712000, by norm_num, R7.Core.Certificates.Terminal025.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_12, 623043477504000000, by norm_num, R7.Core.Certificates.Terminal025.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_13, 73725005581516800000000, by norm_num, R7.Core.Certificates.Terminal025.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_14, 16447679766328463704719360000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_14⟩
theorem bound_101 : minorBindings polynomial_101 witness_101 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_101 witness_101 (by decide +kernel)
theorem positive_101 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_101 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_101 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry016

namespace R7.Core.SpectralSliceCertificates.Entry017
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_102 : BiPoly := r7_rat_grid%[[1042704614126103840,42732487904322477850,171164259842470245600],[0,33952872573596574000,184245048502228800000],[10562108894052483780,865699160367810364200,2302445927861021027700],[0,270800718791973195300,1054844955484959195000],[42271986856255369920,5243847135756315820875,9519137457353676667800],[0,369606199629175110000,2078441610866490375000],[85459859370097570800,12042560915824509193500,16665579117035782047000],[0,-63849263568506923500,1629446967401110200000],[91390860545269451040,11562991901401601556000,12577919713208382153600],[0,-104754135570022310400,401953710824265600000],[48196717444798909560,4063711141610854700400,3202917119062937060400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_102 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal025.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_17, 8280000, by norm_num, R7.Core.Certificates.Terminal025.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_18, 144000, by norm_num, R7.Core.Certificates.Terminal025.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_19, 12960000000, by norm_num, R7.Core.Certificates.Terminal025.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_20, 1224720000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_21, 8332994880000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_22, 1549207877296020480000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_22⟩
theorem bound_102 : minorBindings polynomial_102 witness_102 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_102 witness_102 (by decide +kernel)
theorem positive_102 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_102 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_102 ρ hρ u
noncomputable def polynomial_103 : BiPoly := r7_rat_grid%[[864681875128964160,44008346148115200900,161083974140109374400],[0,18029703091217319000,139316697091860300000],[8329017702015280080,759637603545477983700,1947407513762361944700],[0,143043474289115027100,734419070172080865000],[31545134149958538480,4085474142485533277250,7410898484857333213200],[0,178575178176381636000,1317071097383306850000],[60074213254738200000,8605103349391819515000,11989404330087318750000],[0,-48781052611453674000,933635592843976800000],[60223557125435820480,7669279165250077272000,8358961160068004563200],[0,-54848331795837369600,210459380700254400000],[29632701503131336800,2498484246198355512000,1969243798338876312000],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
noncomputable def witness_103 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal025.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_25, 16560000, by norm_num, R7.Core.Certificates.Terminal025.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_26, 1296000, by norm_num, R7.Core.Certificates.Terminal025.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_27, 5832000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_28, 209952000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_29, 69384936960000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_30, 7371158180020715520000000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_30⟩
theorem bound_103 : minorBindings polynomial_103 witness_103 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_103 witness_103 (by decide +kernel)
theorem positive_103 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_103 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_103 ρ hρ u
noncomputable def polynomial_104 : BiPoly := r7_rat_grid%[[511313430803814720,30671600011258389675,104880413390838274800],[0,4836223503498651000,75443838069728700000],[4613483913892164900,456201778105272778500,1138442008292702653500],[0,47705934705614052600,362643538469313690000],[16288849049736483360,2177762081117381552625,3948139198387173002400],[0,56072175924012084000,588431927052508275000],[28766966118554635200,4167951573337950339000,5834058301682023743000],[0,-24183549986101101000,376087751579653200000],[26631059688657737280,3405778201839947967000,3716812028515232275200],[0,-20156247088301311200,77341846881241800000],[12070968112304971020,1017764906171977171800,802177253146865791800],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
noncomputable def witness_104 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_0, 34500, by norm_num, R7.Core.Certificates.Terminal026.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_1, 62100000, by norm_num, R7.Core.Certificates.Terminal026.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_2, 486000000, by norm_num, R7.Core.Certificates.Terminal026.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_3, 262440000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_4, 2361960000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_5, 1147912560000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_6, 45730990547003520000000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_6⟩
theorem bound_104 : minorBindings polynomial_104 witness_104 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_104 witness_104 (by decide +kernel)
theorem positive_104 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_104 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_104 ρ hρ u
noncomputable def polynomial_105 : BiPoly := r7_rat_grid%[[196761974681049120,13113008982819726300,43072946570540620800],[0,422339772981555000,26827673533303500000],[1633279362619295160,169390631618487977400,416327686751111414400],[0,10471846614970560300,116953339672796445000],[5260577281253980560,715521715468908169500,1296804043805864000400],[0,12033435274256826000,170904089709427725000],[8444717977523198400,1230526323191893068000,1726349583633584256000],[0,-7016846349211636500,98271728622688050000],[7105944127368331440,910565139146124816000,994316681894859489600],[0,-4782353502432211200,18350442455716800000],[2934218482172808840,247398930260817555600,194993748659045595600],[0,0,0],[448932439011941280,-1891153445141188800,2254563784377115200]]
noncomputable def witness_105 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_8, 414000, by norm_num, R7.Core.Certificates.Terminal026.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_9, 298080000, by norm_num, R7.Core.Certificates.Terminal026.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_10, 93312000, by norm_num, R7.Core.Certificates.Terminal026.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_11, 33592320000000, by norm_num, R7.Core.Certificates.Terminal026.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_12, 340122240000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_13, 110199605760000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_14, 975594465002741760000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_14⟩
theorem bound_105 : minorBindings polynomial_105 witness_105 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_105 witness_105 (by decide +kernel)
theorem positive_105 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_105 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_105 ρ hρ u
noncomputable def polynomial_106 : BiPoly := r7_rat_grid%[[10311537095907840,89949596868231600,717955822185105600],[0,448352480901496000,2674889786905200000],[119412440172262080,5196211894623101200,17651690958055012200],[0,6579328460472968400,19271383999757460000],[545812896390269760,53812218201675094500,97890968806684403400],[0,12975323559803235000,49306977922834125000],[1270140508814464800,163983645187688398500,218066958279270882000],[0,-490280035061673000,51324076204574850000],[1577004399619320240,192150450835736661000,206561990128371681600],[0,-4316131241130506400,16561493819184600000],[973230882700882140,82058061027102852600,64676144357208192600],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_106 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_16, 552000, by norm_num, R7.Core.Certificates.Terminal026.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_17, 14720000, by norm_num, R7.Core.Certificates.Terminal026.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_18, 128000, by norm_num, R7.Core.Certificates.Terminal026.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_19, 34560000000, by norm_num, R7.Core.Certificates.Terminal026.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_20, 1866240000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_21, 302330880000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_22, 1338264012349440000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_22⟩
theorem bound_106 : minorBindings polynomial_106 witness_106 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_106 witness_106 (by decide +kernel)
theorem positive_106 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_106 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_106 ρ hρ u
noncomputable def polynomial_107 : BiPoly := r7_rat_grid%[[90424248379499520,1223096358017329800,7385264423863156800],[0,4274337044094708000,21414585963279600000],[1037002769917012800,50099151077813577000,162189600266352402000],[0,54035242187708998800,153666786421670220000],[4741240383569208960,482161638571730745750,877180161526737993900],[0,102811123295551413000,391717881786040425000],[11070819299801754000,1445205057518071147500,1932534353221792110000],[0,-4374009533396898000,407581235351351100000],[13834915091481048480,1693440101047301982000,1823118302845058083200],[0,-34520469151228682400,132459025118448600000],[8628345437676477480,727499824628344693200,573397458928084573200],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
noncomputable def witness_107 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal026.polynomial_24, 276000, by norm_num, R7.Core.Certificates.Terminal026.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal026.polynomial_25, 993600000, by norm_num, R7.Core.Certificates.Terminal026.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal026.polynomial_26, 432000000, by norm_num, R7.Core.Certificates.Terminal026.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal026.polynomial_27, 583200000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal026.polynomial_28, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal026.polynomial_29, 6611976345600000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal026.polynomial_30, 263410505550740275200000000000000000000, by norm_num, R7.Core.Certificates.Terminal026.positive_30⟩
theorem bound_107 : minorBindings polynomial_107 witness_107 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_107 witness_107 (by decide +kernel)
theorem positive_107 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_107 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_107 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry017
