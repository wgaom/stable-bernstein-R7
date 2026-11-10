import R7.Spectral.SliceInteger
import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch03
import R7.Certificates.Spectral.Terminal.Batches.Batch04
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.Entry018
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_108 : BiPoly := r7_rat_grid%[[384303055612872960,7423489309991802900,37910393800840166400],[0,19048199547927498000,82197435229415100000],[4343889380652375840,240115818075197972600,734866050776769413100],[0,205219214143732915200,574948869152641380000],[19610568579633983280,2084751759275060679750,3792091682325336370200],[0,367950710279791845000,1428412271346921375000],[45287374763607640200,6008949146043336091500,8098387542228174318000],[0,-19304465740509960000,1448710645670172000000],[56051720785407021120,6908818460651844408000,7454347752353217580800],[0,-120165212526424675200,461087792134912800000],[34687691759547858960,2924696264667486746400,2305173622761390506400],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
noncomputable def witness_108 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_0, 2622000, by norm_num, R7.Core.Certificates.Terminal027.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_1, 5520000, by norm_num, R7.Core.Certificates.Terminal027.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal027.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_3, 4320000000, by norm_num, R7.Core.Certificates.Terminal027.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_4, 1244160000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_5, 2418647040000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_6, 385420035556638720000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_6⟩
theorem bound_108 : minorBindings polynomial_108 witness_108 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_108 witness_108 (by decide +kernel)
theorem positive_108 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_108 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_108 ρ hρ u
noncomputable def polynomial_109 : BiPoly := r7_rat_grid%[[1031946904752007680,26950158029984488200,122648419579621741200],[0,49654374532192664000,197411902443924300000],[11394984477315377520,724404284820306757800,2100907678543819989300],[0,463811263798244590800,1324658977825570020000],[50308470771016580640,5627034383144215008000,10231023519383459007600],[0,771326496455118903000,3143887736375306925000],[113574591173315048400,15364459294277973115500,20892710783265965631000],[0,-54805749768287374500,3036207975773839650000],[137335511964723166080,17071874584193269512000,18469138127821374067200],[0,-240021517051496073600,920990268608810400000],[82971564208767743040,6995755889355395433600,5513882635348853673600],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_109 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_8, 828000, by norm_num, R7.Core.Certificates.Terminal027.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_9, 3680000, by norm_num, R7.Core.Certificates.Terminal027.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal027.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal027.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_12, 408240000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_13, 22221319680000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_14, 8262442012245442560000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_14⟩
theorem bound_109 : minorBindings polynomial_109 witness_109 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_109 witness_109 (by decide +kernel)
theorem positive_109 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_109 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_109 ρ hρ u
noncomputable def polynomial_110 : BiPoly := r7_rat_grid%[[1917202279375211040,65148512491630265850,269866253422113393600],[0,80891650647274344000,326854713227302800000],[20541689338185675900,1492140453150101938500,4123587495350404206000],[0,672576764412683962800,2072808986439964320000],[87855510165983048160,10350013647814094520750,18806228669055071646900],[0,1026689273474161374000,4614256513492239150000],[191782634800519222200,26475329394943550469000,36324907630436145573000],[0,-106609967511470577000,4152039873468656400000],[223683309303773064480,28052766772299368442000,30432485149295559523200],[0,-305973375340420670400,1174055162235555600000],[129948111591673009320,10956588267887494318800,8635713245068425238800],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_110 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_16, 207000, by norm_num, R7.Core.Certificates.Terminal027.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_17, 41400000, by norm_num, R7.Core.Certificates.Terminal027.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_18, 162000000, by norm_num, R7.Core.Certificates.Terminal027.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_19, 87480000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_20, 16533720000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_21, 337486292640000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_22, 188228757091466488320000000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_22⟩
theorem bound_110 : minorBindings polynomial_110 witness_110 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_110 witness_110 (by decide +kernel)
theorem positive_110 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_110 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_110 ρ hρ u
noncomputable def polynomial_111 : BiPoly := r7_rat_grid%[[2558351843131826880,109210314980259113700,416944311991561969200],[0,82474973498997102000,388047438444092400000],[26348512045641433560,2158230024530566418400,5720976581504486495400],[0,632813641556260641300,2293836488399681595000],[108085209792268680720,13367417189348285060250,24270517463005096827300],[0,882388286709314562000,4710880025509041450000],[225535760619217128000,31733532094799695747500,43893497949181623270000],[0,-142359741847750927500,3877743776822511750000],[250452592485624527040,31664510953404034356000,34436054718540567993600],[0,-262726255150961918400,1008110969693427600000],[137879216993981690640,11625300227899407117600,9162775555800300957600],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_111 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal027.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal027.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal027.polynomial_25, 99360000, by norm_num, R7.Core.Certificates.Terminal027.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal027.polynomial_26, 3456000, by norm_num, R7.Core.Certificates.Terminal027.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal027.polynomial_27, 4665600000000, by norm_num, R7.Core.Certificates.Terminal027.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal027.polynomial_28, 146966400000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal027.polynomial_29, 1999918771200000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal027.polynomial_30, 1115429671653134745600000000000000000, by norm_num, R7.Core.Certificates.Terminal027.positive_30⟩
theorem bound_111 : minorBindings polynomial_111 witness_111 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_111 witness_111 (by decide +kernel)
theorem positive_111 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_111 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_111 ρ hρ u
noncomputable def polynomial_112 : BiPoly := r7_rat_grid%[[2454839874592136640,127151464414345121100,452240618759290947600],[0,49047519998714406000,332389715999947200000],[24074962033414285800,2182936582911000319500,5592454257931983972000],[0,375047670177387840600,1810874391472923390000],[93604875115646225520,12068803963435742810250,21896550815937014296800],[0,480742721725092417000,3387477135875302575000],[184299104235071835000,26348241643321520317500,36685267932237440400000],[0,-127558997649242586000,2523190068115630200000],[192164164264900860480,24451229440120320432000,26643376393811574163200],[0,-156410418018542486400,600164829694029600000],[98833775013385105680,8333179809379221031200,6568007256812605111200],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_112 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_0, 966000, by norm_num, R7.Core.Certificates.Terminal028.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_1, 82800000, by norm_num, R7.Core.Certificates.Terminal028.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_2, 486000000, by norm_num, R7.Core.Certificates.Terminal028.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_3, 364500000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_4, 183708000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_5, 202491775584000000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_6, 75291502836586595328000000000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_6⟩
theorem bound_112 : minorBindings polynomial_112 witness_112 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_112 witness_112 (by decide +kernel)
theorem positive_112 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_112 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_112 ρ hρ u
noncomputable def polynomial_113 : BiPoly := r7_rat_grid%[[1649052740184030720,99186924733724482800,333844188412046464800],[0,13461316723779636000,200666205654298200000],[15163808685559228080,1486291599246034216200,3712709572056540389700],[0,132717051215597786400,998123763811574160000],[55045637924015712960,7321846821196955704500,13276466963904336791400],[0,162257285837934603000,1692535732131926925000],[100667217354011298000,14555538579593142562500,20358817651629786195000],[0,-73103565329433589500,1138702354091265150000],[97058023766212187520,12402452634482193768000,13531802410203622156800],[0,-64561772282834851200,247730973152176800000],[46017842334274546560,3879999064684505030400,3058119780949784390400],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
noncomputable def witness_113 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_8, 552000, by norm_num, R7.Core.Certificates.Terminal028.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_9, 198720000, by norm_num, R7.Core.Certificates.Terminal028.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_10, 432000, by norm_num, R7.Core.Certificates.Terminal028.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_11, 583200000000, by norm_num, R7.Core.Certificates.Terminal028.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_12, 7873200000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_13, 4040652211200000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_14, 643892346901809561600000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_14⟩
theorem bound_113 : minorBindings polynomial_113 witness_113 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_113 witness_113 (by decide +kernel)
theorem positive_113 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_113 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_113 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry018

namespace R7.Core.SpectralSliceCertificates.Entry019
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_114 : BiPoly := r7_rat_grid%[[710752439153993760,47143451175790836150,153474437289186788400],[0,393341911030008000,78876722431952100000],[6020508126711384540,618184929516806145600,1522008238860596321100],[0,29245530187886682600,357886933978935690000],[19966976254515689280,2701748204432519604750,4897473136786805222700],[0,36408267065396025000,549298363019124375000],[33238203990800149800,4833733030522614463500,6776509256352488907000],[0,-24202061922564900000,333616775703873750000],[29154685587118933680,3733111932176213577000,4075551778717837051200],[0,-17221621075445181600,66081348101597400000],[12593898138830818140,1061855804634301092600,836928614294022432600],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
noncomputable def witness_114 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_16, 1863000, by norm_num, R7.Core.Certificates.Terminal028.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_17, 74520000, by norm_num, R7.Core.Certificates.Terminal028.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_18, 104976000, by norm_num, R7.Core.Certificates.Terminal028.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_19, 1049760000000, by norm_num, R7.Core.Certificates.Terminal028.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_20, 37791360000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_21, 18366600960000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_22, 731695848752056320000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_22⟩
theorem bound_114 : minorBindings polynomial_114 witness_114 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_114 witness_114 (by decide +kernel)
theorem positive_114 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_114 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_114 ρ hρ u
noncomputable def polynomial_115 : BiPoly := r7_rat_grid%[[29348220965276160,545548781406858400,2769642149353454400],[0,1504500586691984000,6251721281470800000],[333097859427888960,17810798368006414400,55171327303403231400],[0,16285509410387094000,44630372281841100000],[1523388233208663360,160004437776128547000,291113867931105452400],[0,29614778184291237000,113224320755524575000],[3570124673424441600,471519102782315569500,634155360643382094000],[0,-1445166250412913000,117748594953842850000],[4492263528796071600,552508714857658005000,595726231511590344000],[0,-10065252377427602400,38621535288078600000],[2832537643681671900,238825700004254571000,188236539547098471000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_115 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_24, 368000, by norm_num, R7.Core.Certificates.Terminal028.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_25, 88320000, by norm_num, R7.Core.Certificates.Terminal028.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal028.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_27, 11520000000, by norm_num, R7.Core.Certificates.Terminal028.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_28, 3110400000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_29, 7558272000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_30, 100369800926208000000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_30⟩
theorem bound_115 : minorBindings polynomial_115 witness_115 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_115 witness_115 (by decide +kernel)
theorem positive_115 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_115 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_115 ρ hρ u
noncomputable def polynomial_116 : BiPoly := r7_rat_grid%[[239544938689551360,5604726945617446400,25359909365891222400],[0,12538128658513506000,45286471968217200000],[2708776932328681920,159085071449912733800,473708555937545572800],[0,120572829247326739800,318746858426234370000],[12309302782771606080,1334408583860514336000,2427550930948241797200],[0,209421034027660962000,798330806954968950000],[28715473935764859600,3838246225252361937000,5191739020258807464000],[0,-10991146858235082000,817814596144847400000],[36013502863019695680,4453045186481668512000,4809477803992202131200],[0,-68852161190519251200,264193690666276800000],[22660301149453375200,1910605600034036568000,1505892316376787768000],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
noncomputable def witness_116 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_0, 1472000, by norm_num, R7.Core.Certificates.Terminal029.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_1, 14720000, by norm_num, R7.Core.Certificates.Terminal029.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal029.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_3, 69120000000, by norm_num, R7.Core.Certificates.Terminal029.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_4, 7464960000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_5, 145118822400000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_6, 15416801422265548800000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_6⟩
theorem bound_116 : minorBindings polynomial_116 witness_116 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_116 witness_116 (by decide +kernel)
theorem positive_116 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_116 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_116 ρ hρ u
noncomputable def polynomial_117 : BiPoly := r7_rat_grid%[[941126058791896320,27900137901603459300,115630544217008368800],[0,46806351349813744000,154271286469770300000],[10437066262073854080,686897500998568266200,1958144247799159979700],[0,399334966286709847800,1049512350442052070000],[46556346544214315760,5262287850263180535750,9569245363381765418400],[0,649295011362658401000,2532268142297403975000],[106597400405300454600,14477630220457692349500,19726139637577459764000],[0,-40664926960670439000,2490975775480474800000],[131178283631548130880,16334441694990982332000,17680817895346078099200],[0,-200858847102152870400,770718583140105600000],[80937947438945004240,6824291284224135741600,5378738453109911181600],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_117 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_8, 138000, by norm_num, R7.Core.Certificates.Terminal029.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_9, 1840000, by norm_num, R7.Core.Certificates.Terminal029.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal029.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_11, 1440000000, by norm_num, R7.Core.Certificates.Terminal029.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_12, 181440000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_13, 823011840000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_14, 306016370823905280000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_14⟩
theorem bound_117 : minorBindings polynomial_117 witness_117 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_117 witness_117 (by decide +kernel)
theorem positive_117 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_117 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_117 ρ hρ u
noncomputable def polynomial_118 : BiPoly := r7_rat_grid%[[2287178247388481280,84236907411021920950,325748922356904115200],[0,98426667931349992000,322105084323485400000],[24689569483160555760,1824980081673822453900,4991542461275190930900],[0,754111441173490453200,2079461776365563580000],[106971181231352719680,12654644284768577376000,22997478057050035771200],[0,1132044702117202908000,4729441204326433050000],[237516275148304917600,32836063141137103227000,45089078417274080934000],[0,-96031254913509573000,4358240740728611100000],[282822021437173283520,35489868010847965008000,38507305771980258796800],[0,-328678113439886515200,1261175863320172800000],[168383468541322772640,14197269304868302497600,11189938289384438337600],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
noncomputable def witness_118 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal029.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_17, 21160000, by norm_num, R7.Core.Certificates.Terminal029.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_18, 1104000, by norm_num, R7.Core.Certificates.Terminal029.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_19, 596160000000, by norm_num, R7.Core.Certificates.Terminal029.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_20, 37558080000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_21, 3066542115840000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_22, 2280433995379742146560000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_22⟩
theorem bound_118 : minorBindings polynomial_118 witness_118 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_118 witness_118 (by decide +kernel)
theorem positive_118 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_118 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_118 ρ hρ u
noncomputable def polynomial_119 : BiPoly := r7_rat_grid%[[3760984431639655200,168189656993844891750,612822564755478468000],[0,122279089401888830000,451795134449646000000],[39097754054427980700,3221406721111211785500,8492566046411950263000],[0,860854571633037093000,2721280294613295450000],[162807025885963300800,20133039151244082232500,36560826815198134572000],[0,1183988398053832650000,5719309986775533750000],[346327839413565723000,48715366416378577785000,67385168566421145570000],[0,-153892413687905392500,4832231690297781000000],[393622811299404036000,49755382928668081350000,54107055661353312240000],[0,-335765835915381144000,1288372272653466000000],[222681036295589898600,18775374261872936274000,14798287955164202874000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
noncomputable def witness_119 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_24, 1035000, by norm_num, R7.Core.Certificates.Terminal029.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_25, 23000000, by norm_num, R7.Core.Certificates.Terminal029.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_26, 6000000, by norm_num, R7.Core.Certificates.Terminal029.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_27, 5400000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_28, 6378750000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_29, 217005075000000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_30, 201719775689586000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_30⟩
theorem bound_119 : minorBindings polynomial_119 witness_119 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_119 witness_119 (by decide +kernel)
theorem positive_119 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_119 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_119 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry019

namespace R7.Core.SpectralSliceCertificates.Entry020
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_120 : BiPoly := r7_rat_grid%[[4281469181495118720,226762214659986459050,783338845725416884800],[0,84850446598246318000,439029998583636600000],[42457931085284079120,3843123083900416884300,9825431360152376508300],[0,582689520588974589000,2434646423184175350000],[167849685331718181120,21580356630640986744000,39160578709406432800800],[0,737159504142408102000,4656302719336462950000],[337531258186979058000,48189059363812898205000,67065320266619279220000],[0,-164988458570659374000,3562637743125316800000],[360930860863736587200,45895592011182772320000,50000468657454207648000],[0,-227287642773488774400,872128923026961600000],[191159976363337447200,16117672882338411048000,12703553130460594248000],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
noncomputable def witness_120 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_0, 23000, by norm_num, R7.Core.Certificates.Terminal030.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_1, 920000, by norm_num, R7.Core.Certificates.Terminal030.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_2, 48000, by norm_num, R7.Core.Certificates.Terminal030.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_3, 43200000000, by norm_num, R7.Core.Certificates.Terminal030.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_4, 54432000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_5, 2469035520000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_6, 1836098224943431680000000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_6⟩
theorem bound_120 : minorBindings polynomial_120 witness_120 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_120 witness_120 (by decide +kernel)
theorem positive_120 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_120 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_120 ρ hρ u
noncomputable def polynomial_121 : BiPoly := r7_rat_grid%[[3328147747099408320,201382022743305055550,666781484296780948800],[0,25388231582981492000,293870239611485400000],[30974696624771218440,3016830430487036211600,7537017337959361247100],[0,216418264004439296100,1486325997875773215000],[114484255017859082160,15161689415959137195750,27497260147535359394400],[0,263026687238049627000,2580058370802718575000],[214164570253141683000,30906377964337023787500,43199209805407722720000],[0,-112298967320960070000,1789439723002449000000],[212101856010420022080,27080238045255358572000,29538560695365881107200],[0,-105234659127682963200,403797535185844800000],[103714455260959678800,8744694861694244292000,6892353294186067092000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_121 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal030.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal030.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_10, 432000, by norm_num, R7.Core.Certificates.Terminal030.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_11, 194400000000, by norm_num, R7.Core.Certificates.Terminal030.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_12, 97977600000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_13, 6666395904000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_14, 2478732603673632768000000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_14⟩
theorem bound_121 : minorBindings polynomial_121 witness_121 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_121 witness_121 (by decide +kernel)
theorem positive_121 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_121 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_121 ρ hρ u
noncomputable def polynomial_122 : BiPoly := r7_rat_grid%[[1629421159943744640,107823958162836773600,347715887761407417600],[0,-486960244635372000,126985763026758600000],[13986967663335224160,1424088173202100647400,3510336714053861399400],[0,44208506237170914600,591246313509438990000],[47282060457449637120,6365901859191401784000,11541600697763530090800],[0,58378293301917168000,937348396722679050000],[80602430126928739200,11696938365302293059000,16385648559071948478000],[0,-43658802873696087000,591830513676675900000],[72705557419899497280,9301295300830378992000,10151781800104870675200],[0,-31989139695694886400,122746021785129600000],[32421661644602521440,2733635704664083089600,2154584391123711729600],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
noncomputable def witness_122 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_16, 368000, by norm_num, R7.Core.Certificates.Terminal030.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_17, 29440000, by norm_num, R7.Core.Certificates.Terminal030.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_18, 128000, by norm_num, R7.Core.Certificates.Terminal030.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_19, 23040000000, by norm_num, R7.Core.Certificates.Terminal030.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_20, 622080000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_21, 7255941120000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_22, 770840071113277440000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_22⟩
theorem bound_122 : minorBindings polynomial_122 witness_122 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_122 witness_122 (by decide +kernel)
theorem positive_122 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_122 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_122 ρ hρ u
noncomputable def polynomial_123 : BiPoly := r7_rat_grid%[[61076027414223360,1711265909995006400,7140670384238702400],[0,3260063155872785000,10139793421167000000],[688192747308563040,43920938988943538100,126511623361966323600],[0,27715395802889181900,70112684649434985000],[3107874924968476320,347195416378000074000,631547729611909993800],[0,45480960645248007000,172716761966435325000],[7217487621033546600,976084907061549829500,1327558788842639544000],[0,-2605240928291715000,173410108164738000000],[9022224373917704640,1121505163525518246000,1213286438972920377600],[0,-14295575840404420800,54853774756981200000],[5665075287363343800,477651400008509142000,376473079094196942000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_123 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_24, 736000, by norm_num, R7.Core.Certificates.Terminal030.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_25, 3680000, by norm_num, R7.Core.Certificates.Terminal030.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal030.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_27, 4320000000, by norm_num, R7.Core.Certificates.Terminal030.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_28, 233280000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_29, 1133740800000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_30, 30110940277862400000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_30⟩
theorem bound_123 : minorBindings polynomial_123 witness_123 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_123 witness_123 (by decide +kernel)
theorem positive_123 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_123 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_123 ρ hρ u
noncomputable def polynomial_124 : BiPoly := r7_rat_grid%[[464415766896464640,15557934093650076100,60259524956850717600],[0,23393494399701620000,63248664179619000000],[5144162225315605920,355753541502913951300,993475123849225545300],[0,179289069226599800400,429204915412138260000],[22954690877666904720,2642510859533391185250,4805229735050909487300],[0,277684645425420195000,1031782820774443875000],[52659338933010513600,7205155990759309594500,9851274851624644824000],[0,-14876212271494833000,1006346095812536850000],[65002739117376443040,8122273946334743706000,8801248121184359433600],[0,-79766910571668364800,306074844022147200000],[40265612042490228240,3394999181598941901600,2675854808331061341600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_124 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal031.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_1, 1840000, by norm_num, R7.Core.Certificates.Terminal031.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal031.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_3, 1440000000, by norm_num, R7.Core.Certificates.Terminal031.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_4, 544320000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_5, 22221319680000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_6, 4131221006122721280000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_6⟩
theorem bound_124 : minorBindings polynomial_124 witness_124 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_124 witness_124 (by decide +kernel)
theorem positive_124 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_124 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_124 ρ hρ u
noncomputable def polynomial_125 : BiPoly := r7_rat_grid%[[1651234026877395840,65900847359322685975,241494482840001525600],[0,71801977471976451000,180611593903501200000],[17864467666911286920,1357855637400311003800,3667355271603679335300],[0,495452078587033952100,1171377763173069615000],[77715202661777252880,9284823933771638475375,16874226112838531884200],[0,711440406831778668000,2674580459796004050000],[173597312245263472800,24096465244822645701000,33151291809420431727000],[0,-40253228454159756000,2461120815153949200000],[208260918335915595360,26182978312041627174000,28425692703585973622400],[0,-182719082800463227200,701114213490490800000],[125067431344098436200,10545073215572471058000,8311367207694963258000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_125 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal031.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal031.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal031.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_11, 8640000000, by norm_num, R7.Core.Certificates.Terminal031.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_12, 4354560000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_13, 148142131200000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_14, 82624420122454425600000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_14⟩
theorem bound_125 : minorBindings polynomial_125 witness_125 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_125 witness_125 (by decide +kernel)
theorem positive_125 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_125 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_125 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry020

namespace R7.Core.SpectralSliceCertificates.Entry021
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_126 : BiPoly := r7_rat_grid%[[3555001563209380800,166899157405262898250,585130239463286022000],[0,116796685446382970000,304476301420951500000],[37104273350894329200,3098052117918206663000,8109903021349579128000],[0,730290695027247267000,1843608696289613550000],[155546492394801690000,19312114491444797100000,35073032187122730225000],[0,960245642185296390000,3894286819454159625000],[333840985087045140000,47032682374350714825000,65109169432351441350000],[0,-71941497241593262500,3289079186446252500000],[383507364752045049600,48510584104168436040000,52764652436375988864000],[0,-224644763206355184000,861987889038276000000],[219630611140855790400,18518177354176046736000,14595571681805789136000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
noncomputable def witness_126 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_16, 115000, by norm_num, R7.Core.Certificates.Terminal031.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_17, 138000000, by norm_num, R7.Core.Certificates.Terminal031.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_18, 16000000, by norm_num, R7.Core.Certificates.Terminal031.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_19, 216000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_20, 51030000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_21, 124994923200000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_22, 116190590797201536000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_22⟩
theorem bound_126 : minorBindings polynomial_126 witness_126 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_126 witness_126 (by decide +kernel)
theorem positive_126 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_126 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_126 ρ hρ u
noncomputable def polynomial_127 : BiPoly := r7_rat_grid%[[4985727335266593600,270722156214576417125,912470401309473174000],[0,100108507909391120000,328413326158606500000],[49734233854201785600,4517654536009407821500,11513703864389889204000],[0,583950487341289512000,1821305594655285300000],[198315413380606410000,25499315234236127945625,46277175889210995337500],[0,700348654138252680000,3478943632809078000000],[403226701396267761000,57562596634164203970000,80115473420659004490000],[0,-91937599406642430000,2651787525852801000000],[436870010306228688000,55547048312029861650000,60513528067006633920000],[0,-166381281840001032000,638424185196798000000],[234882736914526331400,19804161892660494426000,15609153048597857826000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
noncomputable def witness_127 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal031.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_25, 34500000, by norm_num, R7.Core.Certificates.Terminal031.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_26, 8000000, by norm_num, R7.Core.Certificates.Terminal031.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_27, 21600000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_28, 136080000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_29, 4629441600000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_30, 4303355214711168000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_30⟩
theorem bound_127 : minorBindings polynomial_127 witness_127 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_127 witness_127 (by decide +kernel)
theorem positive_127 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_127 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_127 ρ hρ u
noncomputable def polynomial_128 : BiPoly := r7_rat_grid%[[4603208968766473920,280837397417840078300,917527210432880602800],[0,35697348509617965000,232542502848783000000],[43126221759230598480,4189700179860887749700,10461008972386039475700],[0,225715903179105375300,1166308989058663695000],[160998511512849272640,21272726601370996525500,38585037882520524725100],[0,256211709520879467000,2016044644134401325000],[305005362724770804000,43967575378974815797500,61433112405789607860000],[0,-78408207550540917000,1398160765140775650000],[306600650857196871840,39124922670509968026000,42669890019289641225600],[0,-82169528359971628800,315293965830043200000],[152521257736705410000,12859845384844476900000,10135813667920686900000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_128 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal032.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_1, 1840000, by norm_num, R7.Core.Certificates.Terminal032.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal032.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_3, 21600000000, by norm_num, R7.Core.Certificates.Terminal032.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_4, 2721600000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_5, 925888320000000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_6, 516402625765340160000000000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_6⟩
theorem bound_128 : minorBindings polynomial_128 witness_128 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_128 witness_128 (by decide +kernel)
theorem positive_128 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_128 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_128 ρ hρ u
noncomputable def polynomial_129 : BiPoly := r7_rat_grid%[[2608918034659836480,172548534932009511450,552539049909091333200],[0,-996728248615510000,104688573392425500000],[22571308017034617240,2285470036974671733600,5637242151957466889100],[0,34724309681878168800,494563570499655720000],[77130694074971255040,10348882876293898589250,18765337416612613766100],[0,47562168829832307000,798746367354684075000],[133278933120869178000,19311397931006351302500,27037461553543994895000],[0,-38524050707655807000,515877440460467400000],[122177002211144627040,15619252794725793906000,17043825719429181993600],[0,-28711282570224004800,110168505604357200000],[55517737816160769240,4680983720083389591600,3689436175123130031600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_129 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_8, 483000, by norm_num, R7.Core.Certificates.Terminal032.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal032.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal032.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_11, 21600000000, by norm_num, R7.Core.Certificates.Terminal032.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_12, 24494400000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_13, 166659897600000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_14, 30984157545920409600000000000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_14⟩
theorem bound_129 : minorBindings polynomial_129 witness_129 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_129 witness_129 (by decide +kernel)
theorem positive_129 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_129 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_129 ρ hρ u
noncomputable def polynomial_130 : BiPoly := r7_rat_grid%[[100259868378673152,3827401363467021480,14106871444806103680],[0,4793309341658749000,11103754882213800000],[1094195043894254112,80812102016644627180,220273776832937365080],[0,32914073566595065500,73524207655646325000],[4830851456110895040,570930760884156370500,1037925072563689803600],[0,47400513266820868200,170909661556768095000],[10959252903757240200,1515543526417554076500,2081927636270162568000],[0,-2303147608989532200,159764286894381540000],[13369981523465790720,1678802349598171938000,1821898233911655244800],[0,-11892958052101156800,45634652949085200000],[8175139414687409976,689287712627663961840,543279612600548817840],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_130 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal032.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_17, 294400, by norm_num, R7.Core.Certificates.Terminal032.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_18, 128, by norm_num, R7.Core.Certificates.Terminal032.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_19, 34560000, by norm_num, R7.Core.Certificates.Terminal032.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_20, 13063680000000, by norm_num, R7.Core.Certificates.Terminal032.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_21, 17777055744000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_22, 660995360979635404800000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_22⟩
theorem bound_130 : minorBindings polynomial_130 witness_130 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_130 witness_130 (by decide +kernel)
theorem positive_130 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_130 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_130 ρ hρ u
noncomputable def polynomial_131 : BiPoly := r7_rat_grid%[[685558577845626624,29650152196903477260,104600336019661136160],[0,28883347895064234600,54260792571355020000],[7375917883482461952,582967068021692387280,1551432230490801595680],[0,177381861353198522100,347638281099815115000],[31936164284685895920,3876836191151325759000,7044817836149904007800],[0,237005366901501290400,777141020830572090000],[70997421630542597280,9921163355076456039600,13689442882136853835200],[0,-5097671872211482200,689515647758159040000],[84705869783536555680,10682795856110053032000,11609021113511866531200],[0,-47571832208404627200,182538611796340800000],[50515040562396831792,4259180791460490749280,3356981486815331501280],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
noncomputable def witness_131 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal032.polynomial_24, 27600, by norm_num, R7.Core.Certificates.Terminal032.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal032.polynomial_25, 584236800, by norm_num, R7.Core.Certificates.Terminal032.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal032.polynomial_26, 746496, by norm_num, R7.Core.Certificates.Terminal032.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal032.polynomial_27, 3708592128000, by norm_num, R7.Core.Certificates.Terminal032.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal032.polynomial_28, 137137287168000000, by norm_num, R7.Core.Certificates.Terminal032.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal032.polynomial_29, 77259198036580761600000000, by norm_num, R7.Core.Certificates.Terminal032.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal032.polynomial_30, 17236140415126834433564344320000000000, by norm_num, R7.Core.Certificates.Terminal032.positive_30⟩
theorem bound_131 : minorBindings polynomial_131 witness_131 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_131 witness_131 (by decide +kernel)
theorem positive_131 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_131 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_131 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry021

namespace R7.Core.SpectralSliceCertificates.Entry022
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_132 : BiPoly := r7_rat_grid%[[2160663619173304320,106554091719346698675,363279013137680338800],[0,69749513500693614000,110534357290051800000],[22489081029723015720,1918157871987775935800,4979039529548205739800],[0,378782810491432519800,659912648458841370000],[94175127395456955120,11793397187876177947125,21417094480963735585800],[0,460205486958396240000,1360418564690154000000],[201952340901499903200,28555836538998850434000,39593833692644346363000],[0,3643460232242796000,1095834766924522800000],[231717026271820491360,29360109503692878624000,31951370179604038262400],[0,-67033036293661065600,257213498440298400000],[132388451715460295880,11162345794045005949200,8797886263755156229200],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_132 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_0, 34500, by norm_num, R7.Core.Certificates.Terminal033.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_1, 135240000, by norm_num, R7.Core.Certificates.Terminal033.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_2, 32000, by norm_num, R7.Core.Certificates.Terminal033.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_3, 17280000000, by norm_num, R7.Core.Certificates.Terminal033.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_4, 243855360000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_5, 7347849707520000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_6, 4098171238073739509760000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_6⟩
theorem bound_132 : minorBindings polynomial_132 witness_132 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_132 witness_132 (by decide +kernel)
theorem positive_132 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_132 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_132 ρ hρ u
noncomputable def polynomial_133 : BiPoly := r7_rat_grid%[[3963695370029881920,220827692577267704550,731421161900056072800],[0,79641572485434967000,111588089635467900000],[39544896031608106800,3626087843679545462000,9203971766118332112000],[0,377388171309367259100,591041147981221665000],[157888599972595758000,20373964492661374593750,36975513709252699470000],[0,407081963289597156000,1050926335120148850000],[321620173704938397600,45981259960842172467000,64038525983647066134000],[0,17016286042679742000,720676378096365600000],[349085526356104614720,44415241345587468888000,48396287537894495404800],[0,-36039266824548960000,138286827118440000000],[187906189531621065120,15843329514128395540800,12487322438878286260800],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
noncomputable def witness_133 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_8, 69000, by norm_num, R7.Core.Certificates.Terminal033.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_9, 901600000, by norm_num, R7.Core.Certificates.Terminal033.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_10, 8000000, by norm_num, R7.Core.Certificates.Terminal033.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_11, 12960000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_12, 3265920000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_13, 88885278720000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_14, 66099536097963540480000000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_14⟩
theorem bound_133 : minorBindings polynomial_133 witness_133 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_133 witness_133 (by decide +kernel)
theorem positive_133 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_133 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_133 ρ hρ u
noncomputable def polynomial_134 : BiPoly := r7_rat_grid%[[4515560903451257280,277963380119587006575,900870100110072205200],[0,36545685961906149000,49551197264106300000],[42344279771611356000,4121685413922297825000,10278691996544659665000],[0,146705996530159682400,201572095882876560000],[158528097172097790480,20954731025562218329125,38009409801360845893200],[0,135767944249168896000,267280125972996600000],[301409491959951474600,43454669811099560442000,60721393161769663689000],[0,12431818309348336500,129912427917965700000],[304167079658846738880,38816008419215478402000,42333524141139556819200],[0,-3243534014209406400,12445814440659600000],[151911172705758588360,12808406003305098992400,10095270413249004152400],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_134 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_16, 103500, by norm_num, R7.Core.Certificates.Terminal033.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_17, 10143000000, by norm_num, R7.Core.Certificates.Terminal033.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_18, 13500000000, by norm_num, R7.Core.Certificates.Terminal033.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_19, 7290000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_20, 2411167500000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_21, 161712181890000000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_22, 90192946106327692320000000000000000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_22⟩
theorem bound_134 : minorBindings polynomial_134 witness_134 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_134 witness_134 (by decide +kernel)
theorem positive_134 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_134 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_134 ρ hρ u
noncomputable def polynomial_135 : BiPoly := r7_rat_grid%[[3040455862123579584,201059440597143785160,642191422992053002560],[0,0,0],[26369932961444264784,2665069228584949137760,6574828309777286170560],[0,0,0],[90429791886271484640,12118437170004704193000,21975052830165736617600],[0,0,0],[156948173143236028800,22728226900195125666000,31814996751478601892000],[0,0,0],[144636225559773564960,18485565633478831104000,20169950222922379286400],[0,0,0],[66133217354635465776,5576028958868565183840,4394888806410409839840],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
noncomputable def witness_135 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal033.polynomial_24, 165600, by norm_num, R7.Core.Certificates.Terminal033.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal033.polynomial_25, 259660800, by norm_num, R7.Core.Certificates.Terminal033.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal033.polynomial_26, 401408, by norm_num, R7.Core.Certificates.Terminal033.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal033.polynomial_27, 433520640000, by norm_num, R7.Core.Certificates.Terminal033.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal033.polynomial_28, 436988805120000000, by norm_num, R7.Core.Certificates.Terminal033.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal033.polynomial_29, 322302666375954432000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal033.polynomial_30, 71904111808090755402458726400000000000, by norm_num, R7.Core.Certificates.Terminal033.positive_30⟩
theorem bound_135 : minorBindings polynomial_135 witness_135 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_135 witness_135 (by decide +kernel)
theorem positive_135 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_135 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_135 ρ hρ u
noncomputable def polynomial_136 : BiPoly := r7_rat_grid%[[128259657569869056,6055982702167470940,20759907228414275040],[0,4834473290029329200,6983175974904540000],[1364444250599899872,113510253990586168580,296870299997329833480],[0,26213213551137775200,42355219377625380000],[5814536638784403600,721347969499618882500,1310347539486278199000],[0,31601275700346228600,88137345386755935000],[12706554306423625560,1791510925274597936700,2481219991108788710400],[0,603923651585704800,70074262358338140000],[14865308404379727840,1882129602438512406000,2047775470592300265600],[0,-3964319350700385600,15211550983028400000],[8663207439444867288,730439217859166287920,575714216337895015920],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_136 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_0, 64400, by norm_num, R7.Core.Certificates.Terminal034.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_1, 220800, by norm_num, R7.Core.Certificates.Terminal034.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_2, 128, by norm_num, R7.Core.Certificates.Terminal034.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_3, 2304000, by norm_num, R7.Core.Certificates.Terminal034.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_4, 3483648000000, by norm_num, R7.Core.Certificates.Terminal034.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_5, 4740548198400000000, by norm_num, R7.Core.Certificates.Terminal034.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_6, 176265429594569441280000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_6⟩
theorem bound_136 : minorBindings polynomial_136 witness_136 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_136 witness_136 (by decide +kernel)
theorem positive_136 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_136 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_136 ρ hρ u
noncomputable def polynomial_137 : BiPoly := r7_rat_grid%[[782883624127772160,40720421694741687150,136127981869414844400],[0,23300409235974866000,15672112159961700000],[8074480658490195120,709427340681736344300,1823238084611491885800],[0,107193106252303561200,85244882537568780000],[33490101747170134080,4249470813617630132250,7715514923652425879700],[0,114854046654800673000,150266441212430175000],[71024884128030477600,10098800584861140544500,14034444740604800334000],[0,15539162733234315000,85785065423835750000],[80395809950314031040,10211920467548965956000,11121585264935479353600],[0,-840916225906142400,3226692632763600000],[45146292290064801360,3806514233913965162400,3000200845704523322400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_137 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_8, 483000, by norm_num, R7.Core.Certificates.Terminal034.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal034.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal034.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal034.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_12, 4898880000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_13, 66663959040000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_14, 12393663018368163840000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_14⟩
theorem bound_137 : minorBindings polynomial_137 witness_137 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_137 witness_137 (by decide +kernel)
theorem positive_137 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_137 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_137 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry022

namespace R7.Core.SpectralSliceCertificates.Entry023
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_138 : BiPoly := r7_rat_grid%[[2100876533896069440,120335075857622138100,394332312219577149600],[0,40051792942527966000,-16239599024793300000],[20852397365081265720,1941978677929432678300,4904675811551466739800],[0,145204107249585266400,-122064852238526340000],[82736138211158391120,10752901693605007666500,19512373281000079825800],[0,126937986621777801000,-320017809956006025000],[167289519853515961800,23990129276507488903500,33452196636118869612000],[0,52313302108182528000,-327399994535304600000],[179849707598550790080,22914200049536755512000,24978431955160886227200],[0,29071675238469494400,-111551373875541600000],[95579988181668723600,8058836441169205524000,6351776565230297124000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_138 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_16, 966000, by norm_num, R7.Core.Certificates.Terminal034.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_17, 5520000, by norm_num, R7.Core.Certificates.Terminal034.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal034.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_19, 1440000000, by norm_num, R7.Core.Certificates.Terminal034.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_20, 2903040000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_21, 65840947200000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_22, 24481309665912422400000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_22⟩
theorem bound_138 : minorBindings polynomial_138 witness_138 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_138 witness_138 (by decide +kernel)
theorem positive_138 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_138 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_138 ρ hρ u
noncomputable def polynomial_139 : BiPoly := r7_rat_grid%[[3139863045703937280,195255740526421099700,631247574752445655200],[0,25223303719525354000,-87036480601247700000],[29311040413336172400,2871907863619930681000,7149041990152410703500],[0,45797080046451210900,-503738933347378665000],[109268483272875944640,14490711243424468458000,26282483948365775517600],[0,9860017885644915000,-983624694658331625000],[206672457657229333200,29838543891934143811500,41717578933591452063000],[0,68236078587033388500,-755245347209491950000],[207117433074040231680,26448239861419313952000,28850638109292968371200],[0,49734188217877564800,-190835821423447200000],[102494285199066035520,8641816098615488476800,6811266784842701596800],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
noncomputable def witness_139 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_24, 322000, by norm_num, R7.Core.Certificates.Terminal034.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_25, 27600000, by norm_num, R7.Core.Certificates.Terminal034.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal034.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_27, 180000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_28, 5670000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_29, 925888320000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_30, 344268417176893440000000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_30⟩
theorem bound_139 : minorBindings polynomial_139 witness_139 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_139 witness_139 (by decide +kernel)
theorem positive_139 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_139 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_139 ρ hρ u
noncomputable def polynomial_140 : BiPoly := r7_rat_grid%[[132066994343742720,7308704268378002800,24065203942394044800],[0,3204064574543298000,-510236507799900000],[1332391437711555840,121614773058648835100,308874952748047800600],[0,11902877821274035200,-5898047401855620000],[5415360042916892880,698885968533880836000,1268470307124780109200],[0,10243102115410029000,-20021977786988475000],[11216713817706118200,1605720934764184486500,2237541360809379588000],[0,4008386744077158000,-25543025849145600000],[12352153982675631840,1573313274700767126000,1714899025272779625600],[0,2591394900241377600,-9943481378516400000],[6710935340415038040,565833196933156983600,445975801388510223600],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_140 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_0, 184000, by norm_num, R7.Core.Certificates.Terminal035.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_1, 7360000, by norm_num, R7.Core.Certificates.Terminal035.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal035.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_3, 33120000000, by norm_num, R7.Core.Certificates.Terminal035.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_4, 622080000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_5, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_6, 16059168148193280000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_6⟩
theorem bound_140 : minorBindings polynomial_140 witness_140 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_140 witness_140 (by decide +kernel)
theorem positive_140 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_140 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_140 ρ hρ u
noncomputable def polynomial_141 : BiPoly := r7_rat_grid%[[681751241071752960,40282031807757970400,131225137197221366400],[0,11049223783198944000,-26388935730052200000],[6685525433328620400,636240797520344311000,1596989144295764586000],[0,26108831664107180400,-159367735170214740000],[26137920568181798880,3432073730719030716000,6226392097375847899200],[0,11347954010711586000,-338983838621485650000],[51921284313023730000,7477236099649335105000,10443489774481222200000],[0,26728574171552946000,-286725667374907200000],[54610845583630006080,6970067480008362672000,7602011172724155667200],[0,20525220534362169600,-78757640587454400000],[28238221432395744480,2380908516965491723200,1876573501946458603200],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
noncomputable def witness_141 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_8, 368000, by norm_num, R7.Core.Certificates.Terminal035.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_9, 147200000, by norm_num, R7.Core.Certificates.Terminal035.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_10, 16000000, by norm_num, R7.Core.Certificates.Terminal035.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_11, 1656000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_12, 178848000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_13, 56324242944000000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_14, 5983646052016816128000000000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_14⟩
theorem bound_141 : minorBindings polynomial_141 witness_141 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_141 witness_141 (by decide +kernel)
theorem positive_141 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_141 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_141 ρ hρ u
noncomputable def polynomial_142 : BiPoly := r7_rat_grid%[[1496461821043625280,94194010889176357200,305083081077925075200],[0,10445274162051354000,-93998471898647700000],[13813348260190027320,1368593058524722827300,3398223184432189408800],[0,-7816987085890613400,-512145428526001710000],[50888906127252501840,6787973842737823458000,12309592275765468165600],[0,-35571041093613519000,-944800011321990525000],[94857182729231617800,13729061716844552473500,19212513466268590902000],[0,54172821211762491000,-685014884169451200000],[93330178040684445120,11930782958532068508000,13018727949047621740800],[0,42011488184045644800,-161202929898067200000],[45146292290064801360,3806514233913965162400,3000200845704523322400],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
noncomputable def witness_142 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_16, 552000, by norm_num, R7.Core.Certificates.Terminal035.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_17, 198720000, by norm_num, R7.Core.Certificates.Terminal035.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_18, 3888000, by norm_num, R7.Core.Certificates.Terminal035.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_19, 349920000000, by norm_num, R7.Core.Certificates.Terminal035.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_20, 6298560000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_21, 12244400640000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_22, 1951188930005483520000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_22⟩
theorem bound_142 : minorBindings polynomial_142 witness_142 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_142 witness_142 (by decide +kernel)
theorem positive_142 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_142 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_142 ρ hρ u
noncomputable def polynomial_143 : BiPoly := r7_rat_grid%[[104404313096066880,6416155817750491200,20773682328108319200],[0,1160273658528087000,-6342115678613100000],[1005185639476377180,98252812850761660200,244809809699917246200],[0,575769005389777500,-36892910091625875000],[3826800120587003280,508575448412817261000,922362870781571920200],[0,-2284562555027118000,-74734970761877175000],[7371964169402873400,1066448557530241533000,1492101763215615756000],[0,4677950170849657500,-58909903919154000000],[7476634404569685600,955860232651707105000,1043053280544649104000],[0,3835607683469853600,-14717669457605400000],[3704087687891417100,312310530774794439000,246155474792359539000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_143 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_24, 9936000, by norm_num, R7.Core.Certificates.Terminal035.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_25, 33120000, by norm_num, R7.Core.Certificates.Terminal035.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_26, 1296000, by norm_num, R7.Core.Certificates.Terminal035.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_27, 5365440000000, by norm_num, R7.Core.Certificates.Terminal035.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_28, 7873200000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_29, 19131876000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_30, 254061058594464000000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_30⟩
theorem bound_143 : minorBindings polynomial_143 witness_143 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_143 witness_143 (by decide +kernel)
theorem positive_143 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_143 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_143 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry023

namespace R7.Core.SpectralSliceCertificates.Entry024
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_144 : BiPoly := r7_rat_grid%[[445726105910131680,28546795360764594450,92705510419278901200],[0,2022889882344678000,-40634658575568900000],[4037240329245097560,406042655594530028400,1004797024937310942900],[0,-11555226653436246600,-214141104491407290000],[14565872518594064640,1957461616163825894250,3548948930109769130100],[0,-21112193029910733000,-378648228415687425000],[26466981953944658400,3841979806746259240500,5382397328836680531000],[0,19446337817729892000,-260496850456758150000],[25238353279963384080,3230066554322105097000,3525842844781074187200],[0,14982038065633924800,-57487809559237200000],[11765925596831560200,992045215402288218000,781905625811024418000],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
noncomputable def witness_144 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_0, 1863000, by norm_num, R7.Core.Certificates.Terminal036.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_1, 74520000, by norm_num, R7.Core.Certificates.Terminal036.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_2, 34992000, by norm_num, R7.Core.Certificates.Terminal036.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_3, 9447840000000, by norm_num, R7.Core.Certificates.Terminal036.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_4, 3061100160000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_5, 401677562995200000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_6, 16002188212207471718400000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_6⟩
theorem bound_144 : minorBindings polynomial_144 witness_144 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_144 witness_144 (by decide +kernel)
theorem positive_144 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_144 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_144 ρ hρ u
noncomputable def polynomial_145 : BiPoly := r7_rat_grid%[[64248808059118080,4205013696475301700,13676663761581427200],[0,62773198789455000,-6915885568366500000],[562102637784562620,57480763626308341800,141684957863874460800],[0,-2759751147004647300,-35289275411992995000],[1961260519491902160,265466320787688889500,481201027541646944400],[0,-3930077599415568000,-59232393838415925000],[3424230155520077400,498290437877977098000,698721040891834866000],[0,2762091680323423500,-38251554350672700000],[3116311482913079040,399172490076565431000,435836205325355673600],[0,2050805897873143200,-7869178971739800000],[1379954236665429900,116350982053354791000,91704980804996691000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_145 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_8, 414000, by norm_num, R7.Core.Certificates.Terminal036.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_9, 149040000, by norm_num, R7.Core.Certificates.Terminal036.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_10, 11664000, by norm_num, R7.Core.Certificates.Terminal036.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_11, 2099520000000, by norm_num, R7.Core.Certificates.Terminal036.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_12, 14171760000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_13, 11479125600000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_14, 50812211718892800000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_14⟩
theorem bound_145 : minorBindings polynomial_145 witness_145 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_145 witness_145 (by decide +kernel)
theorem positive_145 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_145 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_145 ρ hρ u
noncomputable def polynomial_146 : BiPoly := r7_rat_grid%[[1031153709590784,8994959686823160,71795582218510560],[0,40132433449154400,262319825339280000],[11312757490003776,455868639489080640,1606198108432974840],[0,653247157874101200,1966755654219780000],[52951997410996320,5050792393311327750,9186265109942106300],[0,1402657447223721600,5306875476911235000],[127014050881446480,16196828059179498600,21402437291280650700],[0,-47206170627359400,5693226977725830000],[160213594383636120,19426175735030140500,20850312070913680800],[0,-480523557660652800,1843824361579200000],[98775671677104456,8328280820661185040,6564145994462921040],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
noncomputable def witness_146 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal036.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_17, 2649600, by norm_num, R7.Core.Certificates.Terminal036.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_18, 27648, by norm_num, R7.Core.Certificates.Terminal036.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_19, 1492992000, by norm_num, R7.Core.Certificates.Terminal036.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_20, 241864704000000, by norm_num, R7.Core.Certificates.Terminal036.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_21, 15672832819200000000, by norm_num, R7.Core.Certificates.Terminal036.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_22, 6937560640019496960000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_22⟩
theorem bound_146 : minorBindings polynomial_146 witness_146 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_146 witness_146 (by decide +kernel)
theorem positive_146 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_146 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_146 ρ hρ u
noncomputable def polynomial_147 : BiPoly := r7_rat_grid%[[8725146773460480,93085899273697700,611959221694243200],[0,369740863730269000,2165381835787800000],[99510366810218400,4216830420768798500,14461188934862218500],[0,5620195226885202300,16547423137891245000],[473852489652249120,45937722250482655875,83565718155467358300],[0,12040355747135475000,45506426148360000000],[1158574112769951000,148551205582320547500,196858465120667340000],[0,-435768182439349500,50178050549865900000],[1499515471616777280,182187055072551447000,195671061187673875200],[0,-4384777463653456800,16824897299410200000],[953863103940665580,80425064787757522200,63389056907313502200],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_147 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal036.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal036.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal036.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_27, 900000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_28, 4050000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_29, 218700000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_30, 968072925600000000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_30⟩
theorem bound_147 : minorBindings polynomial_147 witness_147 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_147 witness_147 (by decide +kernel)
theorem positive_147 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_147 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_147 ρ hρ u
noncomputable def polynomial_148 : BiPoly := r7_rat_grid%[[37875068948430720,580711510736792800,3076279104251464800],[0,1741264278881196000,8672119329670200000],[434179442556163440,20645275813752856600,67140471457357172100],[0,23080138164950604000,66153395076447600000],[2066146206671375640,207585924300744349875,377646773772702432600],[0,47607028962633810000,180962284736966625000],[5054815943862971400,656224535457049023000,875087683544455326000],[0,-1997512756671492000,199609335018396900000],[6576087403459051200,802932259073975235000,863729356315029408000],[0,-17607756077136777600,67562992677866400000],[4227017714417264220,356401429237118359800,280906835939516179800],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
noncomputable def witness_148 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal037.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_1, 14720000, by norm_num, R7.Core.Certificates.Terminal037.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal037.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_3, 8640000000, by norm_num, R7.Core.Certificates.Terminal037.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_4, 1555200000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_5, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_6, 15055470138931200000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_6⟩
theorem bound_148 : minorBindings polynomial_148 witness_148 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_148 witness_148 (by decide +kernel)
theorem positive_148 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_148 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_148 ρ hρ u
noncomputable def polynomial_149 : BiPoly := r7_rat_grid%[[106486450394279040,2224722323617143350,10375390769667513600],[0,5135645782600087000,22134965623911900000],[1213764605698321800,66291735708193539500,203511826629617899500],[0,58544101234546700700,165550345723230705000],[5708632643962410960,601538633256863734500,1094170992565412111400],[0,113633023291724718000,441513185915940300000],[13799904987659860800,1823392312702130466000,2452400025702975522000],[0,-6102567581548464000,474865026976504800000],[17768001761447958720,2185743977292805668000,2356863503578800364800],[0,-41084764179985814400,157646982915021600000],[11330150574726687600,955302800017018284000,752946158188393884000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_149 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal037.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_9, 4600000, by norm_num, R7.Core.Certificates.Terminal037.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal037.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_11, 720000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_12, 311040000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_13, 3023308800000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_14, 160591681481932800000000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_14⟩
theorem bound_149 : minorBindings polynomial_149 witness_149 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_149 witness_149 (by decide +kernel)
theorem positive_149 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_149 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_149 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry024

namespace R7.Core.SpectralSliceCertificates.Entry025
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_150 : BiPoly := r7_rat_grid%[[213195986927652240,5832235776285793850,24955979673642351600],[0,9967353280387745000,39705009284281500000],[2388772542217926960,150353544973236730650,437168849694512463900],[0,99397686914814404400,286936982504748360000],[10999080282730286880,1222394855907618804750,2222572240577008069200],[0,179040975956665578000,732744758597946300000],[25986388247906752800,3505041716065942851000,4759430917953715677000],[0,-13454641907718669000,751098335778573300000],[32677290368207508240,4056489989963390511000,4386616982876255601600],[0,-61987538938224211200,237853342643716800000],[20336167698227388000,1714646051312596920000,1351441822389424920000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_150 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal037.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_17, 460000, by norm_num, R7.Core.Certificates.Terminal037.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_18, 6000, by norm_num, R7.Core.Certificates.Terminal037.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_19, 1080000000, by norm_num, R7.Core.Certificates.Terminal037.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_20, 204120000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_21, 46294416000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_22, 4303355214711168000000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_22⟩
theorem bound_150 : minorBindings polynomial_150 witness_150 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_150 witness_150 (by decide +kernel)
theorem positive_150 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_150 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_150 ρ hρ u
noncomputable def polynomial_151 : BiPoly := r7_rat_grid%[[315354566223504576,10974203492367276990,43681212875679171840],[0,12877343561766297600,52339686816610620000],[3444970338153858204,248105232197339349060,687210979068613840860],[0,115476085486984023000,360408071284587450000],[15386628478464507600,1804521804302566869375,3278928057312080371500],[0,191367137559889279800,866345940690612705000],[35155429596672794640,4843952989575895842300,6640127508442988307600],[0,-21452857181508778200,828734902388661240000],[42631476173507148480,5342350270860150282000,5794137207967712083200],[0,-63789502279451659200,244767683999638800000],[25501554293577144552,2150166148345996537680,1694708045276338849680],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
noncomputable def witness_151 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_24, 41400, by norm_num, R7.Core.Certificates.Terminal037.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_25, 146059200, by norm_num, R7.Core.Certificates.Terminal037.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_26, 31104, by norm_num, R7.Core.Certificates.Terminal037.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_27, 1679616000, by norm_num, R7.Core.Certificates.Terminal037.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_28, 211631616000000, by norm_num, R7.Core.Certificates.Terminal037.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_29, 287988303052800000000, by norm_num, R7.Core.Certificates.Terminal037.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_30, 32124374543610280673280000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_30⟩
theorem bound_151 : minorBindings polynomial_151 witness_151 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_151 witness_151 (by decide +kernel)
theorem positive_151 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_151 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_151 ρ hρ u
noncomputable def polynomial_152 : BiPoly := r7_rat_grid%[[349352893821454560,15031665973665290650,56031855430690010400],[0,10780165119420588000,51518393798385600000],[3682538245443937500,299406217085044920000,795293636924807437500],[0,90631249785454902600,333672626133116190000],[15798024766042248240,1948119904939276144875,3537161088476164716600],[0,137828717799455214000,743330318521756275000],[34516926530079577200,4851916783983511456500,6708041965331021898000],[0,-24202124834568219000,651678672115270800000],[39846063356118442080,5036254609704978492000,5476587154655715907200],[0,-46130261535422668800,177007138711603200000],[22573146145032400680,1903257116956982581200,1500100422852261661200],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_152 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_0, 23000, by norm_num, R7.Core.Certificates.Terminal038.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_1, 1035000000, by norm_num, R7.Core.Certificates.Terminal038.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_2, 11250000000, by norm_num, R7.Core.Certificates.Terminal038.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_3, 1012500000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_4, 3444525000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_5, 23436548100000000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_6, 2178573577447528800000000000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_6⟩
theorem bound_152 : minorBindings polynomial_152 witness_152 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_152 witness_152 (by decide +kernel)
theorem positive_152 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_152 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_152 ρ hρ u
noncomputable def polynomial_153 : BiPoly := r7_rat_grid%[[286442602596901440,14794814843949960600,51958954632866529600],[0,5312616056398827000,37646908785099900000],[2884753159950962880,259919100767490065700,667086375694866896700],[0,46024037301788035500,226857634772039325000],[11749233579386068080,1512465108117236574750,2744093592917389627200],[0,64895979420370836000,462477796375564350000],[24235654033054382400,3464132700700737243000,4822601919671494566000],[0,-18703827847343556000,367410188136859200000],[26262463706807803200,3341911294489931460000,3641605833599525088000],[0,-23785916104202313600,91269305898170400000],[13886697371075273520,1170858303610601896800,922841701574493016800],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_153 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_8, 276000, by norm_num, R7.Core.Certificates.Terminal038.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_9, 33120000, by norm_num, R7.Core.Certificates.Terminal038.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_10, 1296000, by norm_num, R7.Core.Certificates.Terminal038.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_11, 5365440000000, by norm_num, R7.Core.Certificates.Terminal038.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_12, 1007769600000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_13, 653034700800000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_14, 34687803200097484800000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_14⟩
theorem bound_153 : minorBindings polynomial_153 witness_153 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_153 witness_153 (by decide +kernel)
theorem positive_153 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_153 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_153 ρ hρ u
noncomputable def polynomial_154 : BiPoly := r7_rat_grid%[[167983862737902480,10006224255700442700,33504734300588773200],[0,1117867079525829000,19816383286347300000],[1590856522031781000,155116008566554496250,388054058124200602500],[0,14193327710655386400,110028549363576660000],[6060967088274040320,805818263081368760250,1461147932781780441300],[0,19402267657572378000,203994382412723175000],[11620069249559360400,1680739265218788063000,2351105748906632023500],[0,-9394616649230478000,146351310715963350000],[11636952120165674520,1487435428003676800500,1623017667296694736800],[0,-8649424037891750400,33188838508425600000],[5665075287363343800,477651400008509142000,376473079094196942000],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
noncomputable def witness_154 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_16, 138000, by norm_num, R7.Core.Certificates.Terminal038.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_17, 621000000, by norm_num, R7.Core.Certificates.Terminal038.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_18, 37968750000, by norm_num, R7.Core.Certificates.Terminal038.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_19, 10251562500000000, by norm_num, R7.Core.Certificates.Terminal038.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_20, 184528125000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_21, 896806687500000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_22, 17863668182423250000000000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_22⟩
theorem bound_154 : minorBindings polynomial_154 witness_154 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_154 witness_154 (by decide +kernel)
theorem positive_154 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_154 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_154 ρ hρ u
noncomputable def polynomial_155 : BiPoly := r7_rat_grid%[[7138756451013120,96222201679163800,505962621203380800],[0,338157392968994000,1707565418182800000],[85893158720399040,3874974446646790600,12860396785394688600],[0,4707918875029392600,13427289733584690000],[418185005194535040,41367520567852034250,75268785211513653600],[0,10054137022033734000,37944097527607650000],[1047007716725437200,135134130572846109000,179692557328528173000],[0,-399474658605105000,43423831322473500000],[1396894999397193360,170112352794801489000,182839001666210942400],[0,-3964319350700385600,15211550983028400000],[919969491110286600,77567321368903194000,61136653869997794000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_155 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_24, 92000, by norm_num, R7.Core.Certificates.Terminal038.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_25, 7360000, by norm_num, R7.Core.Certificates.Terminal038.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal038.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_27, 23040000000, by norm_num, R7.Core.Certificates.Terminal038.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_28, 207360000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_29, 2575411200000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_30, 11400026771865600000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_30⟩
theorem bound_155 : minorBindings polynomial_155 witness_155 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_155 witness_155 (by decide +kernel)
theorem positive_155 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_155 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_155 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry025
