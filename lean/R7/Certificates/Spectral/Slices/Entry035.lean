import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal052
import R7.Certificates.Spectral.Terminal.Terminal053

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry035
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_210 : BiPoly := [[1546234817410411200,73440873032020681750,227778616410784008000],[0,13855066706256320000,-9658086605091000000],[18150167167411150800,1433307251005196312000,3777821042095789384500],[0,59500084598241609000,-69604043093049150000],[86688529607656090800,10489071904075384447500,19063107747585345672000],[0,59416631600077350000,-186539617992268125000],[213950019491517618000,29879770231536704460000,41223807478133415495000],[0,31983718411473097500,-241501282595149500000],[284405308722846864000,35863764318459132300000,38971774896656333760000],[0,31234031247942432000,-119848583502648000000],[189126359593514708400,15946208277207151356000,12568408948221651756000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
def witness_210 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_16, 115000, by norm_num, R7.Core.Certificates.Terminal052.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_17, 69000000, by norm_num, R7.Core.Certificates.Terminal052.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_18, 2000000, by norm_num, R7.Core.Certificates.Terminal052.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_19, 1800000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_20, 708750000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_21, 48223350000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_22, 44826616819908000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_22⟩
theorem bound_210 : minorBindings polynomial_210 witness_210 := by
 decide +kernel
theorem positive_210 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_210 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_210 ρ hρ u
def polynomial_211 : BiPoly := [[360507200776162560,17713720960140258775,55782563391091730400],[0,1098158379820114000,-10695448111723200000],[4140416867464113480,337966986509435714700,883257187129341950700],[0,-6555307814118660600,-79230289775856390000],[19415053512270304560,2386109387248921834500,4335069319328495660400],[0,-21877646017917915000,-210729851635312125000],[46900796491020609000,6591652685745283282500,9117401280925523310000],[0,13046797001951811000,-237419357723912700000],[60809959823833442880,7688879593587843462000,8362117092518252179200],[0,22944999878296171200,-88042613265406800000],[39248803657578858840,3309266879033312055600,2608282717211590095600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_211 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_24, 11500, by norm_num, R7.Core.Certificates.Terminal052.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_25, 460000, by norm_num, R7.Core.Certificates.Terminal052.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal052.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_27, 21600000000, by norm_num, R7.Core.Certificates.Terminal052.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_28, 2721600000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_29, 6172588800000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_30, 1147561390589644800000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_30⟩
theorem bound_211 : minorBindings polynomial_211 witness_211 := by
 decide +kernel
theorem positive_211 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_211 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_211 ρ hρ u
def polynomial_212 : BiPoly := [[3271930040047680,110481330969579450,321837413376841200],[0,138365110058763000,472874749208100000],[40066016110430040,2287442104032131850,6708281991294603600],[0,1613502479987731800,4019768526956670000],[209262220537687380,22209607239058757250,40444350576155989200],[0,3392120759035068000,12530853004144050000],[566414010687531600,75127414155381927000,101311157346308694000],[0,-191991865738752000,16282085952978900000],[829340959162351680,102142501699127157000,110180366856817171200],[0,-1750478674335235200,6716788745752800000],[610085030946821640,51439381539377907600,40543254671682747600],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
def witness_212 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal053.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_1, 4140000, by norm_num, R7.Core.Certificates.Terminal053.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_2, 54000, by norm_num, R7.Core.Certificates.Terminal053.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_3, 29160000000, by norm_num, R7.Core.Certificates.Terminal053.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_4, 217300320000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_5, 9183300480000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_6, 30487327031335680000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_6⟩
theorem bound_212 : minorBindings polynomial_212 witness_212 := by
 decide +kernel
theorem positive_212 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_212 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_212 ρ hρ u
def polynomial_213 : BiPoly := [[24093303022169280,843324393744602825,2341163642334535200],[0,922125671017299000,3047668796323800000],[303637553464337460,17833266895378631900,51515510343060033900],[0,10534312107332378100,26073677985654015000],[1594669768185004560,170685405292451683875,310838761613668347900],[0,22221968803553376000,81739219934660850000],[4351089445736038200,579316363575519879000,782767792185562638000],[0,-1292074197002649000,106958772939084300000],[6433675319562485760,794144206708919874000,857241178505728358400],[0,-11652696273270830400,44712740768295600000],[4793525243153598600,404166569237969274000,318554143848935874000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_213 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal053.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal053.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal053.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_11, 2880000000, by norm_num, R7.Core.Certificates.Terminal053.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_12, 77760000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_13, 377913600000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_14, 10036980092620800000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_14⟩
theorem bound_213 : minorBindings polynomial_213 witness_213 := by
 decide +kernel
theorem positive_213 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_213 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_213 ρ hρ u
def polynomial_214 : BiPoly := [[88961794800993360,3398621295902240775,9513254770371752400],[0,2838361855921701000,8899161627638700000],[1113337696035904020,70207799715578340300,197622418510363749300],[0,30593526280867001400,75316967782051410000],[5782969101866309640,635500896436934858625,1156933613668275867600],[0,62809085482378434000,232654749963549525000],[15610713415766969400,2099320943622549295500,2849710006485836271000],[0,-4007931999094611000,299943830186147700000],[22855045170047333040,2834164616044118931000,3063794171143272033600],[0,-32195078363263737600,123536232225806400000],[16879019189528732040,1423156222589455443600,1121696712583222683600],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_214 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_16, 34500, by norm_num, R7.Core.Certificates.Terminal053.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_17, 4140000, by norm_num, R7.Core.Certificates.Terminal053.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_18, 432000, by norm_num, R7.Core.Certificates.Terminal053.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_19, 38880000000, by norm_num, R7.Core.Certificates.Terminal053.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_20, 4898880000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_21, 11110659840000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_22, 1032805251530680320000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_22⟩
theorem bound_214 : minorBindings polynomial_214 witness_214 := by
 decide +kernel
theorem positive_214 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_214 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_214 ρ hρ u
def polynomial_215 : BiPoly := [[205883719035121440,8578932701569361225,24916635405640329600],[0,4701478447306283000,15253511059119600000],[2535288463876656420,174394216269236571300,477755968424364465300],[0,48587262179558612700,125331231465076005000],[12873445216727220720,1466392176125020259625,2668005033540888552300],[0,95977221966833112000,373694272353058950000],[33924766427997157800,4626617388089034636000,6319262493648355752000],[0,-8065405326698118000,464514055321692600000],[48407542752723729120,6040854609904984338000,6543205407334726300800],[0,-47932224876650116800,183921480067525200000],[34774846763968833480,2932044747744540733200,2310965516285916613200],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_215 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_24, 11500, by norm_num, R7.Core.Certificates.Terminal053.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_25, 460000, by norm_num, R7.Core.Certificates.Terminal053.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal053.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_27, 8640000000, by norm_num, R7.Core.Certificates.Terminal053.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_28, 2177280000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_29, 844410147840000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_30, 156986398232663408640000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_30⟩
theorem bound_215 : minorBindings polynomial_215 witness_215 := by
 decide +kernel
theorem positive_215 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_215 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_215 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry035
