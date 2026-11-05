import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal042
import R7.Certificates.Spectral.Terminal.Terminal043

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry028
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_168 : BiPoly := [[3967363897650541440,205196732144532677475,689891359416507129600],[0,53780258066142762000,346334053496684400000],[42044963063021672760,3697290720538006631400,9513845961822995648400],[0,478409683420885556700,2189995075355007105000],[180067340426663062800,22878564665222891047500,41528003608389054402000],[0,719892225896580495000,4796057527135367625000],[394395792047821245600,56082465847045345684500,77926353907092515829000],[0,-200864349435718741500,4186908652489249050000],[459681075273896199360,58370395227777982944000,63563807095980430982400],[0,-302729841326211264000,1161609347794896000000],[264776903430920591760,22324691588090011898400,17595772527510312458400],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
def witness_168 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_0, 103500, by norm_num, R7.Core.Certificates.Terminal042.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_1, 3651480000, by norm_num, R7.Core.Certificates.Terminal042.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_2, 23328000, by norm_num, R7.Core.Certificates.Terminal042.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_3, 6298560000000, by norm_num, R7.Core.Certificates.Terminal042.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_4, 1785641760000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_5, 170093091490560000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_6, 189734587148198220226560000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_6⟩
theorem bound_168 : minorBindings polynomial_168 witness_168 := by
 decide +kernel
theorem positive_168 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_168 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_168 ρ hρ u
def polynomial_169 : BiPoly := [[3068326757101076640,178291923418883309225,585894047729748297600],[0,3296789985064584000,223790638777840800000],[30600223402301186040,2896360557676189519350,7288607935061895581100],[0,135580179775643408400,1303306707273780960000],[122845579070583904920,16097307080598960177750,29201474129511639817800],[0,219727257820462368000,2608567336172242800000],[250801258308067022400,36075623319608780853000,50360060165377263291000],[0,-138139662738247128000,2071851698540087100000],[270947366794621429920,34558324520656300938000,37683944544625088572800],[0,-138390784606268006400,531021416134809600000],[143980067303449907040,12139694043293186193600,9568208102517128433600],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_169 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal042.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_9, 690000, by norm_num, R7.Core.Certificates.Terminal042.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_10, 54000, by norm_num, R7.Core.Certificates.Terminal042.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_11, 9720000000, by norm_num, R7.Core.Certificates.Terminal042.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_12, 4898880000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_13, 133327918080000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_14, 74361978110208983040000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_14⟩
theorem bound_169 : minorBindings polynomial_169 witness_169 := by
 decide +kernel
theorem positive_169 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_169 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_169 ρ hρ u
def polynomial_170 : BiPoly := [[76939930638696960,2364791498884715400,8428518412320326400],[0,3705005938347572000,11738960689181400000],[921780239926233600,57514943505886479000,165607692871095774000],[0,35489656296095092200,90345473605271430000],[4484626857654380640,494357200984203408000,899509364631817257600],[0,65893041241217622000,249965527821417450000],[11293952091890781600,1518908601796526547000,2060916800513309694000],[0,-4053068518638069000,282984976147578300000],[15338619153800665920,1901479688987372748000,2055336787705904812800],[0,-26360149448812953600,101146936406630400000],[10458600530516942400,881817969246478416000,695027222943132816000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_170 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_16, 828000, by norm_num, R7.Core.Certificates.Terminal042.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_17, 36800000, by norm_num, R7.Core.Certificates.Terminal042.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_18, 432000000, by norm_num, R7.Core.Certificates.Terminal042.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_19, 77760000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_20, 699840000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_21, 81629337600000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_22, 4335975400012185600000000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_22⟩
theorem bound_170 : minorBindings polynomial_170 witness_170 := by
 decide +kernel
theorem positive_170 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_170 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_170 ρ hρ u
def polynomial_171 : BiPoly := [[577446077370839040,20375725672867839600,69998675810926413600],[0,25496109480310988000,71588864239703100000],[6813841432636533600,457460239756136264000,1281197724365248524000],[0,223169243529730746300,543170351550912345000],[32808514498443976320,3719443264076515134000,6765795595207716868800],[0,393919870428011169000,1473856896401149275000],[81718094087373877200,11112294858731765266500,15153732896434757523000],[0,-23970195907007395500,1629360381690086850000],[109774585140034913280,13677245728446458592000,14807309825288952115200],[0,-147040208644159756800,564210254643235200000],[74023650421547692320,6241311626777852788800,4919248233497506708800],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_171 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal042.polynomial_24, 552000, by norm_num, R7.Core.Certificates.Terminal042.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal042.polynomial_25, 294400000, by norm_num, R7.Core.Certificates.Terminal042.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal042.polynomial_26, 64000000, by norm_num, R7.Core.Certificates.Terminal042.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal042.polynomial_27, 51840000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal042.polynomial_28, 14696640000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal042.polynomial_29, 133327918080000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal042.polynomial_30, 49574652073472655360000000000000000000, by norm_num, R7.Core.Certificates.Terminal042.positive_30⟩
theorem bound_171 : minorBindings polynomial_171 witness_171 := by
 decide +kernel
theorem positive_171 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_171 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_171 ρ hρ u
def polynomial_172 : BiPoly := [[2031967704264762240,82406542412241157600,278090296229474001600],[0,74590270283749290000,197873428917685500000],[23476066746848576640,1726165937224037539600,4686664343557100547600],[0,595284204244975712100,1446540301624038615000],[110364182296226560800,12978047932070685622500,23594294760800872347000],[0,981754830780715035000,3754077781711789125000],[267982483298922147600,36968180375525428579500,50729645246273241759000],[0,-67774535320761769500,3941158798092666150000],[350316972022739621760,43922960748085815144000,47645156521726066598400],[0,-335165181468305328000,1286067492201492000000],[229391971636004936640,19341207458806093257600,15244263756552713097600],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
def witness_172 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal043.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_1, 721280000, by norm_num, R7.Core.Certificates.Terminal043.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_2, 1024000, by norm_num, R7.Core.Certificates.Terminal043.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_3, 276480000000, by norm_num, R7.Core.Certificates.Terminal043.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_4, 8709120000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_5, 474054819840000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_6, 528796288783708323840000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_6⟩
theorem bound_172 : minorBindings polynomial_172 witness_172 := by
 decide +kernel
theorem positive_172 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_172 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_172 ρ hρ u
def polynomial_173 : BiPoly := [[4340760519796588800,201058420116040699500,671123020019673492000],[0,111693717115453990000,319052594117875500000],[48479879493620348400,3909401434150718988500,10306777551186030043500],[0,826226456312422834500,2199813614750988675000],[219995183089839326400,26894739140742418162500,48860352318766366251000],[0,1263474791963070660000,5331126028613098500000],[513977804546610114000,71994870996466195755000,99432209104390909260000],[0,-125811377643117127500,5175117655169789250000],[644163364189788206400,81291300553231550460000,88356739394457598176000],[0,-407243715117403248000,1562641146438372000000],[402656120424902282400,33949991815989419016000,26758548083310613416000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
def witness_173 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_8, 2070000, by norm_num, R7.Core.Certificates.Terminal043.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_9, 46000000, by norm_num, R7.Core.Certificates.Terminal043.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal043.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_11, 5400000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_12, 425250000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_13, 173604060000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_14, 322751641103337600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_14⟩
theorem bound_173 : minorBindings polynomial_173 witness_173 := by
 decide +kernel
theorem positive_173 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_173 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_173 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry028
