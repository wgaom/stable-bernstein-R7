import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal027
import R7.Certificates.Spectral.Terminal.Terminal028

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry018
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_108 : BiPoly := [[384303055612872960,7423489309991802900,37910393800840166400],[0,19048199547927498000,82197435229415100000],[4343889380652375840,240115818075197972600,734866050776769413100],[0,205219214143732915200,574948869152641380000],[19610568579633983280,2084751759275060679750,3792091682325336370200],[0,367950710279791845000,1428412271346921375000],[45287374763607640200,6008949146043336091500,8098387542228174318000],[0,-19304465740509960000,1448710645670172000000],[56051720785407021120,6908818460651844408000,7454347752353217580800],[0,-120165212526424675200,461087792134912800000],[34687691759547858960,2924696264667486746400,2305173622761390506400],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
def witness_108 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_0, 2622000, by norm_num, R7.Core.Certificates.Terminal027.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_1, 5520000, by norm_num, R7.Core.Certificates.Terminal027.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal027.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_3, 4320000000, by norm_num, R7.Core.Certificates.Terminal027.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_4, 1244160000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_5, 2418647040000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_6, 385420035556638720000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_6⟩
theorem bound_108 : minorBindings polynomial_108 witness_108 := by
 decide +kernel
theorem positive_108 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_108 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_108 ρ hρ u
def polynomial_109 : BiPoly := [[1031946904752007680,26950158029984488200,122648419579621741200],[0,49654374532192664000,197411902443924300000],[11394984477315377520,724404284820306757800,2100907678543819989300],[0,463811263798244590800,1324658977825570020000],[50308470771016580640,5627034383144215008000,10231023519383459007600],[0,771326496455118903000,3143887736375306925000],[113574591173315048400,15364459294277973115500,20892710783265965631000],[0,-54805749768287374500,3036207975773839650000],[137335511964723166080,17071874584193269512000,18469138127821374067200],[0,-240021517051496073600,920990268608810400000],[82971564208767743040,6995755889355395433600,5513882635348853673600],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_109 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_8, 828000, by norm_num, R7.Core.Certificates.Terminal027.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_9, 3680000, by norm_num, R7.Core.Certificates.Terminal027.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal027.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal027.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_12, 408240000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_13, 22221319680000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_14, 8262442012245442560000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_14⟩
theorem bound_109 : minorBindings polynomial_109 witness_109 := by
 decide +kernel
theorem positive_109 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_109 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_109 ρ hρ u
def polynomial_110 : BiPoly := [[1917202279375211040,65148512491630265850,269866253422113393600],[0,80891650647274344000,326854713227302800000],[20541689338185675900,1492140453150101938500,4123587495350404206000],[0,672576764412683962800,2072808986439964320000],[87855510165983048160,10350013647814094520750,18806228669055071646900],[0,1026689273474161374000,4614256513492239150000],[191782634800519222200,26475329394943550469000,36324907630436145573000],[0,-106609967511470577000,4152039873468656400000],[223683309303773064480,28052766772299368442000,30432485149295559523200],[0,-305973375340420670400,1174055162235555600000],[129948111591673009320,10956588267887494318800,8635713245068425238800],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_110 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_16, 207000, by norm_num, R7.Core.Certificates.Terminal027.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_17, 41400000, by norm_num, R7.Core.Certificates.Terminal027.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_18, 162000000, by norm_num, R7.Core.Certificates.Terminal027.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_19, 87480000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_20, 16533720000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_21, 337486292640000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_22, 188228757091466488320000000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_22⟩
theorem bound_110 : minorBindings polynomial_110 witness_110 := by
 decide +kernel
theorem positive_110 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_110 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_110 ρ hρ u
def polynomial_111 : BiPoly := [[2558351843131826880,109210314980259113700,416944311991561969200],[0,82474973498997102000,388047438444092400000],[26348512045641433560,2158230024530566418400,5720976581504486495400],[0,632813641556260641300,2293836488399681595000],[108085209792268680720,13367417189348285060250,24270517463005096827300],[0,882388286709314562000,4710880025509041450000],[225535760619217128000,31733532094799695747500,43893497949181623270000],[0,-142359741847750927500,3877743776822511750000],[250452592485624527040,31664510953404034356000,34436054718540567993600],[0,-262726255150961918400,1008110969693427600000],[137879216993981690640,11625300227899407117600,9162775555800300957600],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_111 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal027.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_25, 99360000, by norm_num, R7.Core.Certificates.Terminal027.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_26, 3456000, by norm_num, R7.Core.Certificates.Terminal027.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_27, 4665600000000, by norm_num, R7.Core.Certificates.Terminal027.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_28, 146966400000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_29, 1999918771200000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_30, 1115429671653134745600000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_30⟩
theorem bound_111 : minorBindings polynomial_111 witness_111 := by
 decide +kernel
theorem positive_111 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_111 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_111 ρ hρ u
def polynomial_112 : BiPoly := [[2454839874592136640,127151464414345121100,452240618759290947600],[0,49047519998714406000,332389715999947200000],[24074962033414285800,2182936582911000319500,5592454257931983972000],[0,375047670177387840600,1810874391472923390000],[93604875115646225520,12068803963435742810250,21896550815937014296800],[0,480742721725092417000,3387477135875302575000],[184299104235071835000,26348241643321520317500,36685267932237440400000],[0,-127558997649242586000,2523190068115630200000],[192164164264900860480,24451229440120320432000,26643376393811574163200],[0,-156410418018542486400,600164829694029600000],[98833775013385105680,8333179809379221031200,6568007256812605111200],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_112 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_0, 966000, by norm_num, R7.Core.Certificates.Terminal028.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_1, 82800000, by norm_num, R7.Core.Certificates.Terminal028.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_2, 486000000, by norm_num, R7.Core.Certificates.Terminal028.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_3, 364500000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_4, 183708000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_5, 202491775584000000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_6, 75291502836586595328000000000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_6⟩
theorem bound_112 : minorBindings polynomial_112 witness_112 := by
 decide +kernel
theorem positive_112 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_112 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_112 ρ hρ u
def polynomial_113 : BiPoly := [[1649052740184030720,99186924733724482800,333844188412046464800],[0,13461316723779636000,200666205654298200000],[15163808685559228080,1486291599246034216200,3712709572056540389700],[0,132717051215597786400,998123763811574160000],[55045637924015712960,7321846821196955704500,13276466963904336791400],[0,162257285837934603000,1692535732131926925000],[100667217354011298000,14555538579593142562500,20358817651629786195000],[0,-73103565329433589500,1138702354091265150000],[97058023766212187520,12402452634482193768000,13531802410203622156800],[0,-64561772282834851200,247730973152176800000],[46017842334274546560,3879999064684505030400,3058119780949784390400],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
def witness_113 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_8, 552000, by norm_num, R7.Core.Certificates.Terminal028.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_9, 198720000, by norm_num, R7.Core.Certificates.Terminal028.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_10, 432000, by norm_num, R7.Core.Certificates.Terminal028.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_11, 583200000000, by norm_num, R7.Core.Certificates.Terminal028.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_12, 7873200000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_13, 4040652211200000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_14, 643892346901809561600000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_14⟩
theorem bound_113 : minorBindings polynomial_113 witness_113 := by
 decide +kernel
theorem positive_113 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_113 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_113 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry018
