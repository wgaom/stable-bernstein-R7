import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal015
import R7.Certificates.Spectral.Terminal.Terminal016

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry010
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_60 : BiPoly := [[1841283587506589568,112334958967136031320,367010884173152241120],[0,12962510804311945200,82847412917953740000],[14920898642787758112,1451951129754723057180,3623171225612222350080],[0,67336553204279543100,336410095140986265000],[48903206224340139840,6466979131675302535500,11729887739394234960600],[0,64106824531380777000,481211608997402325000],[82301672158991334000,11867726312985771945000,16584225557094330435000],[0,-15075841953813070500,280998548873434350000],[74238581617138995840,9474487578346678776000,10333265032460183385600],[0,-14055314061574094400,53931862576191600000],[33432659695885825872,2818878108357909336480,2221770356008214568480],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
def witness_60 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_0, 18400, by norm_num, R7.Core.Certificates.Terminal015.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_1, 441600, by norm_num, R7.Core.Certificates.Terminal015.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_2, 3456, by norm_num, R7.Core.Certificates.Terminal015.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_3, 3110400000, by norm_num, R7.Core.Certificates.Terminal015.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_4, 146966400000000, by norm_num, R7.Core.Certificates.Terminal015.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_5, 399983754240000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_6, 44617186866125389824000000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_6⟩
theorem bound_60 : minorBindings polynomial_60 witness_60 := by
 decide +kernel
theorem positive_60 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_60 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_60 ρ hρ u
def polynomial_61 : BiPoly := [[1043567213863934592,69019413972803804580,221015619963636533280],[0,-358766499906020400,36977580280474020000],[7774064098477872624,786906989020110155360,1941016698948277901160],[0,9798149996068221300,140115518323771095000],[23251357837520820000,3118638578346247102500,5655014112779786925000],[0,11109008847982311000,187180426170452475000],[35666918612384565600,5166933590630703627000,7233609983538116754000],[0,-7656352959364861500,102433269488514300000],[29378775189720882240,3755422117732781916000,4097809770953920761600],[0,-4925366466021691200,18899199706186800000],[12120355948143523248,1021929046582307764320,805459326144097252320],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_61 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_8, 193200, by norm_num, R7.Core.Certificates.Terminal015.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_9, 441600, by norm_num, R7.Core.Certificates.Terminal015.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_10, 1024, by norm_num, R7.Core.Certificates.Terminal015.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_11, 184320000, by norm_num, R7.Core.Certificates.Terminal015.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_12, 8709120000000, by norm_num, R7.Core.Certificates.Terminal015.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_13, 7900913664000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_14, 293775715990949068800000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_14⟩
theorem bound_61 : minorBindings polynomial_61 witness_61 := by
 decide +kernel
theorem positive_61 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_61 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_61 ρ hρ u
def polynomial_62 : BiPoly := [[298162061103981312,19719832563658229880,63147319989610438080],[0,-96821053465823600,10119010976635680000],[1910703790510730352,193453928234470968280,477168885193568251680],[0,2480307834419869200,35325969321403980000],[5008715857670908320,671989036832940969000,1218502038995021998800],[0,2603797141560714000,43683281513159400000],[6831296250110229600,989784951511179357000,1385759874026499264000],[0,-1657953199209006000,22215064391674200000],[5059817569030913280,646842597904243512000,705835212309864115200],[0,-995370226582780800,3819350463271200000],[1894168762749179568,159707032207973313120,125877152599700721120],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
def witness_62 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal015.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_17, 294400, by norm_num, R7.Core.Certificates.Terminal015.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_18, 1024, by norm_num, R7.Core.Certificates.Terminal015.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_19, 184320000, by norm_num, R7.Core.Certificates.Terminal015.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_20, 6635520000000, by norm_num, R7.Core.Certificates.Terminal015.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_21, 859963392000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_22, 4567941162152755200000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_22⟩
theorem bound_62 : minorBindings polynomial_62 witness_62 := by
 decide +kernel
theorem positive_62 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_62 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_62 ρ hρ u
def polynomial_63 : BiPoly := [[33419956126224384,1275800454489007160,4702290481602034560],[0,1476641418125122400,3372610242080880000],[316966705229179872,23644810331959628580,64217759878928283480],[0,8608494303413064600,18862747813211490000],[1232831119209863040,146711948491756000500,266689357078190673600],[0,10583402465604074400,37478541326828490000],[2490505240932146520,345676864663840541400,475613717184301906800],[0,-389887893308239200,30133805710703940000],[2726772547548944160,343043379158424084000,372503286463192214400],[0,-1922094230642611200,7375297446316800000],[1504876409668826712,126883807797132172080,100006694856817444080],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
def witness_63 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal015.polynomial_24, 18400, by norm_num, R7.Core.Certificates.Terminal015.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal015.polynomial_25, 147200, by norm_num, R7.Core.Certificates.Terminal015.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal015.polynomial_26, 384, by norm_num, R7.Core.Certificates.Terminal015.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal015.polynomial_27, 13824000, by norm_num, R7.Core.Certificates.Terminal015.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal015.polynomial_28, 41803776000000, by norm_num, R7.Core.Certificates.Terminal015.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal015.polynomial_29, 18962192793600000000, by norm_num, R7.Core.Certificates.Terminal015.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal015.polynomial_30, 117510286396379627520000000000, by norm_num, R7.Core.Certificates.Terminal015.positive_30⟩
theorem bound_63 : minorBindings polynomial_63 witness_63 := by
 decide +kernel
theorem positive_63 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_63 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_63 ρ hρ u
def polynomial_64 : BiPoly := [[228519525948542208,9883384065634492420,34866778673220378720],[0,8889461922625517000,16400625736077900000],[2141672589264974112,170677545675271167180,452926316951338915080],[0,46214545662613243800,87585305313454470000],[8179725856475572560,998854833400263252000,1814893897893586655400],[0,52543282803156910800,165350653626452805000],[16194291487384426200,2270023857700630389000,3136306475826045558000],[0,-334616330824990200,124370229265255890000],[17328199737649741920,2188758435402988008000,2379660558651186652800],[0,-7207853364909792000,27657365423688000000],[9313964805788143704,785307891501169389360,618960354654356613360],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_64 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_0, 9200, by norm_num, R7.Core.Certificates.Terminal016.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_1, 73600, by norm_num, R7.Core.Certificates.Terminal016.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_2, 1152, by norm_num, R7.Core.Certificates.Terminal016.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_3, 207360000, by norm_num, R7.Core.Certificates.Terminal016.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_4, 39191040000000, by norm_num, R7.Core.Certificates.Terminal016.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_5, 17777055744000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_6, 660995360979635404800000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_6⟩
theorem bound_64 : minorBindings polynomial_64 witness_64 := by
 decide +kernel
theorem positive_64 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_64 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_64 ρ hρ u
def polynomial_65 : BiPoly := [[720221206391101440,35518030573115566225,121093004379226779600],[0,21408336864511411000,32947319065115700000],[6534426797408894040,560739122344518356850,1452616828853209676100],[0,97814363255323948200,159756178182735330000],[24142037588844245280,3036622748589873761625,5514120752436378700200],[0,100510729604604306000,270133261961485725000],[46094085627314124600,6532299153997076907000,9065617270358569501500],[0,3109117080228138000,178431685660812150000],[47410658165447771040,6013657737573414516000,6546539314816546953600],[0,-8649424037891750400,33188838508425600000],[24403401237872865600,2057575261575116304000,1621730186867309904000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_65 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal016.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal016.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal016.polynomial_9, 230000, by norm_num, R7.Core.Certificates.Terminal016.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal016.polynomial_10, 18000, by norm_num, R7.Core.Certificates.Terminal016.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal016.polynomial_11, 1620000000, by norm_num, R7.Core.Certificates.Terminal016.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal016.polynomial_12, 17146080000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal016.polynomial_13, 666639590400000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal016.polynomial_14, 61968315091840819200000000000000000, by norm_num, R7.Core.Certificates.Terminal016.positive_14⟩
theorem bound_65 : minorBindings polynomial_65 witness_65 := by
 decide +kernel
theorem positive_65 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_65 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_65 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry010
