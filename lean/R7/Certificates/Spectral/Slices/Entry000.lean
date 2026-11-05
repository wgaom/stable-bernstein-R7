import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal000
import R7.Certificates.Spectral.Terminal.Terminal001

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry000
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_0 : BiPoly := [[105759354829824,-708981990042240,2860714298924160],[0,1444308557961600,28036958209920000],[837982036296576,23520976850612640,100380901894701840],[0,43801073573313600,139183004265840000],[2715487046717760,244900443711132000,445269755583473400],[0,66614708353629600,250905825641160000],[4577082914646720,576406904489735400,756691126293124800],[0,-1383169684496400,187088766180480000],[4188590702840160,506060044538049000,542529634740854400],[0,-11441037087158400,43900580037600000],[1936777876021656,163299623934533040,128708744989469040],[0,0,0],[340100332584804,-1432692003894840,1708002866952360]]
def witness_0 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_0, 883200, by norm_num, R7.Core.Certificates.Terminal000.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_1, 84787200, by norm_num, R7.Core.Certificates.Terminal000.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_2, 221184, by norm_num, R7.Core.Certificates.Terminal000.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_3, 7962624000, by norm_num, R7.Core.Certificates.Terminal000.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_4, 1146617856000000, by norm_num, R7.Core.Certificates.Terminal000.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_5, 24766945689600000000, by norm_num, R7.Core.Certificates.Terminal000.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_6, 166106951351009280000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_6⟩
theorem bound_0 : minorBindings polynomial_0 witness_0 := by
 decide +kernel
theorem positive_0 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_0 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_0 ρ hρ u
def polynomial_1 : BiPoly := [[951834193468416,-6380837910380160,25746428690317440],[0,13359854161144800,259341863441760000],[7960829344817472,223449280080820080,953618567999667480],[0,427060467339807600,1357034291591940000],[27154870467177600,2449004437111320000,4452697555834734000],[0,682800760624703400,2571784712821890000],[48059370603790560,6052272497142221700,7945256826077810400],[0,-14869074108336300,2011204236440160000],[46074497731241760,5566660489918539000,5967825982149398400],[0,-128711667230532000,493881525423000000],[22272945574249044,1877945675247129960,1480150567378893960],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
def witness_1 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_8, 7948800, by norm_num, R7.Core.Certificates.Terminal000.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_9, 190771200, by norm_num, R7.Core.Certificates.Terminal000.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_10, 27648, by norm_num, R7.Core.Certificates.Terminal000.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_11, 1492992000, by norm_num, R7.Core.Certificates.Terminal000.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_12, 6718464000000, by norm_num, R7.Core.Certificates.Terminal000.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_13, 72559411200000000, by norm_num, R7.Core.Certificates.Terminal000.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_14, 5839697508433920000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_14⟩
theorem bound_1 : minorBindings polynomial_1 witness_1 := by
 decide +kernel
theorem positive_1 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_1 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_1 ρ hρ u
def polynomial_2 : BiPoly := [[4521212418974976,-14401445984570760,166199154083007840],[0,87794615861887200,1187539446266640000],[38547173669642496,1220300387133991440,4868577420010784640],[0,2032980975433479600,6351020288593740000],[134416608812529120,12397805704645287750,22544357777446308300],[0,3267869281125350400,12332238594863715000],[243729665204937840,30895204123667751300,40698061011755333100],[0,-78327488528528400,9902724216786630000],[239796817737599160,29041316581253071500,31158375130989914400],[0,-652139113968028800,2502333062143200000],[119111839375331844,10042926871973781960,7915587816852345960],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
def witness_2 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal000.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_17, 15897600, by norm_num, R7.Core.Certificates.Terminal000.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_18, 442368, by norm_num, R7.Core.Certificates.Terminal000.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_19, 23887872000, by norm_num, R7.Core.Certificates.Terminal000.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_20, 429981696000000, by norm_num, R7.Core.Certificates.Terminal000.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_21, 13931406950400000000, by norm_num, R7.Core.Certificates.Terminal000.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_22, 6166720568906219520000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_22⟩
theorem bound_2 : minorBindings polynomial_2 witness_2 := by
 decide +kernel
theorem positive_2 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_2 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_2 ρ hρ u
def polynomial_3 : BiPoly := [[14277512902026240,17836086054365100,741973101721761600],[0,394871340019647000,3548357969621400000],[122554872808374240,4598490215418671100,16826127480517769100],[0,6230524454179236900,18965691381383235000],[430404696904764960,41302289484838877625,75114877892493033900],[0,9690643523406645000,36858118518032625000],[786686125954905000,100989888576508732500,133898457051229950000],[0,-275830012429587000,29697873907219650000],[781172166079689840,95073988620843801000,102167312299929345600],[0,-1970718638263034400,7561874911476600000],[392197519894385340,33068173846742940600,26063520860367480600],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
def witness_3 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_24, 414000, by norm_num, R7.Core.Certificates.Terminal000.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_25, 16560000, by norm_num, R7.Core.Certificates.Terminal000.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_26, 432000, by norm_num, R7.Core.Certificates.Terminal000.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_27, 972000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_28, 17496000000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_29, 76527504000000000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_30, 112916026041984000000000000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_30⟩
theorem bound_3 : minorBindings polynomial_3 witness_3 := by
 decide +kernel
theorem positive_3 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_3 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_3 ρ hρ u
def polynomial_4 : BiPoly := [[33016748585935680,217179004622731950,2352740551072261200],[0,1164861934360749000,7650569737851300000],[282033329091066360,12693005198445369150,42723202207586634900],[0,13468824530444068200,40204163909838330000],[985891515898966740,99517262750633341125,180987638173833756600],[0,19760275636761762000,76703033950208325000],[1793644367177183400,234291418281003190500,313320486980067156000],[0,-724732400026656000,60664174205141700000],[1772821014977097720,217311970265968720500,234060577297486624800],[0,-3964319350700385600,15211550983028400000],[886075878279907620,74709577950048865800,58884250832682085800],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
def witness_4 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal001.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_1, 12420000, by norm_num, R7.Core.Certificates.Terminal001.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_2, 486000, by norm_num, R7.Core.Certificates.Terminal001.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_3, 131220000000, by norm_num, R7.Core.Certificates.Terminal001.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_4, 2361960000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_5, 8800662960000000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_6, 29217021738363360000000000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_6⟩
theorem bound_4 : minorBindings polynomial_4 witness_4 := by
 decide +kernel
theorem positive_4 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_4 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_4 ρ hρ u
def polynomial_5 : BiPoly := [[58359333987032256,758867818044112065,5449337030903963040],[0,2335848979481579400,12516968373861780000],[491869268367455844,26421790298720688660,82564528689499215960],[0,21264731638104928500,63696262796392275000],[1694463917151882240,180923431143842168625,328962207011702714100],[0,28951581662012611800,117231486258852405000],[3034605972410775360,404519586276043982700,546216346135936742400],[0,-1457336480226190200,89180832551489640000],[2948767854799472640,364591755128758446000,393767287906681497600],[0,-5611828691251195200,21533234508442800000],[1446773073388177032,121984819079096180880,96145432507133372880],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
def witness_5 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_8, 20700, by norm_num, R7.Core.Certificates.Terminal001.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_9, 165600, by norm_num, R7.Core.Certificates.Terminal001.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_10, 3456, by norm_num, R7.Core.Certificates.Terminal001.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_11, 186624000, by norm_num, R7.Core.Certificates.Terminal001.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_12, 3359232000000, by norm_num, R7.Core.Certificates.Terminal001.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_13, 653034700800000000, by norm_num, R7.Core.Certificates.Terminal001.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_14, 3468780320009748480000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_14⟩
theorem bound_5 : minorBindings polynomial_5 witness_5 := by
 decide +kernel
theorem positive_5 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_5 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_5 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry000
