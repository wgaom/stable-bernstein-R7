import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal024
import R7.Certificates.Spectral.Terminal.Terminal025

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry016
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_96 : BiPoly := [[2538224515915776,4194477691966240,127195300246179840],[0,73369153937511200,735267942505440000],[28910380252231872,995920970687216080,3797882359173213480],[0,1714166876785088400,5301613704410460000],[130343378242452480,12122199619393341000,22044288102759223200],[0,3518923961383961400,13285753153833690000],[295221847994713440,37446960619040388300,49345589028101799600],[0,-104782443792495300,13250404480593960000],[351841619038573440,42601549116462471000,45703894040999769600],[0,-1049715152746783200,4027878218449800000],[206266843796306364,17391409949027768760,13707481341378452760],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
def witness_96 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_0, 73600, by norm_num, R7.Core.Certificates.Terminal024.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_1, 1177600, by norm_num, R7.Core.Certificates.Terminal024.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_2, 1024, by norm_num, R7.Core.Certificates.Terminal024.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_3, 18432000, by norm_num, R7.Core.Certificates.Terminal024.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_4, 248832000000, by norm_num, R7.Core.Certificates.Terminal024.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_5, 8062156800000000, by norm_num, R7.Core.Certificates.Terminal024.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_6, 7137408065863680000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_6⟩
theorem bound_96 : minorBindings polynomial_96 witness_96 := by
 decide +kernel
theorem positive_96 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_96 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_96 ρ hρ u
def polynomial_97 : BiPoly := [[23002659675486720,110921985328062800,1353932323416004800],[0,815198250589052000,6351229499432400000],[263964341433421440,10175816748059181600,36641102753921079600],[0,15150162844398410400,45779452521809760000],[1197529787602532160,114423216298641799500,208112409320480519400],[0,30569943366723042000,115735743692002575000],[2746249748788032000,351218448282890340000,464794903419779880000],[0,-1014192254024149500,117576098607544650000],[3336212494812187440,405158196418049016000,435081460333370529600],[0,-9564707004864422400,36700884911433600000],[2004565101682413960,169015110772241696400,133213551064100456400],[0,0,0],[448932439011941280,-1891153445141188800,2254563784377115200]]
def witness_97 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_8, 184000, by norm_num, R7.Core.Certificates.Terminal024.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_9, 29440000, by norm_num, R7.Core.Certificates.Terminal024.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_10, 3072000, by norm_num, R7.Core.Certificates.Terminal024.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_11, 5529600000000, by norm_num, R7.Core.Certificates.Terminal024.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_12, 167961600000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_13, 163258675200000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_14, 1445325133337395200000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_14⟩
theorem bound_97 : minorBindings polynomial_97 witness_97 := by
 decide +kernel
theorem positive_97 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_97 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_97 ρ hρ u
def polynomial_98 : BiPoly := [[103908566120302080,1015069519982256700,7781760206395987200],[0,4389980417363637000,26565382233959400000],[1180507193632801440,53187522473673369100,178208451325754342100],[0,63760195843375494300,188059290036471045000],[5319639124520091840,531054800896386143625,965933841781561890600],[0,122322381708919176000,468602146689131475000],[12160737168852004200,1578230672292016209000,2104062427940145453000],[0,-4923896554999093500,472272539553529200000],[14787819476377184880,1806302379485682432000,1943324379040786459200],[0,-38459046168482961600,147571799796392400000],[8933387953149888300,753219515398033647000,593669086263925947000],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
def witness_98 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal024.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal024.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal024.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_19, 8640000000, by norm_num, R7.Core.Certificates.Terminal024.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_20, 19440000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_21, 47239200000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_22, 1881933767366400000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_22⟩
theorem bound_98 : minorBindings polynomial_98 witness_98 := by
 decide +kernel
theorem positive_98 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_98 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_98 ρ hρ u
def polynomial_99 : BiPoly := [[301017563684386560,4754281717097516900,28539847539347390400],[0,14049635267005093000,70602788615804100000],[3362402920640011200,178670735549077120500,558493360877214445500],[0,164978626659957063300,483357787830095895000],[14905987271195464080,1569463003613881967250,2854230030649945267200],[0,294947064446496048000,1164659974377839550000],[33572903178933691200,4441557879506354859000,5976573381415894158000],[0,-15755299584852168000,1136553619896327600000],[40285865379916658880,4960715937385973832000,5350768796933217619200],[0,-90132490172633875200,345848769536212800000],[24054781220188967520,2028181329266900356800,1598562612769205476800],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
def witness_99 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal024.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal024.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal024.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal024.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal024.polynomial_26, 6000000, by norm_num, R7.Core.Certificates.Terminal024.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal024.polynomial_27, 1080000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal024.polynomial_28, 933120000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal024.polynomial_29, 10883911680000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal024.polynomial_30, 1156260106669916160000000000000000000, by norm_num, R7.Core.Certificates.Terminal024.positive_30⟩
theorem bound_99 : minorBindings polynomial_99 witness_99 := by
 decide +kernel
theorem positive_99 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_99 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_99 ρ hρ u
def polynomial_100 : BiPoly := [[616312640270799360,14187689523640518275,72214923452899292400],[0,28784006023349590000,131723434754320500000],[6713938261746801180,418305878049549117700,1228830075765174593700],[0,285014397170579888400,860449718333780460000],[29029914272936213280,3235533259742050875375,5881684161040896445200],[0,468894424712528619000,1969883716435744275000],[63747322293742192800,8616836333253310213500,11710784684023839027000],[0,-35569521491377072500,1821140493772257000000],[74531782966337807040,9263847483255837906000,10021705544329163193600],[0,-137069344822701211200,525950899140466800000],[43316037197224336440,3652196089295831439600,2878571081689475079600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_100 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_0, 11500, by norm_num, R7.Core.Certificates.Terminal025.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_1, 1380000, by norm_num, R7.Core.Certificates.Terminal025.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal025.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_3, 1440000000, by norm_num, R7.Core.Certificates.Terminal025.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_4, 45360000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_5, 308629440000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_6, 57378069529482240000000000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_6⟩
theorem bound_100 : minorBindings polynomial_100 witness_100 := by
 decide +kernel
theorem positive_100 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_100 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_100 ρ hρ u
def polynomial_101 : BiPoly := [[928127573087343264,29242889922407080860,130605245633298533760],[0,38787976888322923800,180405849684729060000],[9793548432075352248,706029824682570510720,1965304949374652557320],[0,337076609571458831700,1109992125309323355000],[40938003844555270320,4825155710433379246500,8765745082180542703800],[0,506037216139141579200,2375049681100916820000],[86740298315469990720,11981954446312496720400,16441473222973514584800],[0,-56969089701730970400,2038850392546929780000],[97606729148284248480,12246641094302159832000,13287371052988706083200],[0,-142715496625213881600,547615835389022400000],[54419584760456490288,4588392833312509357920,3616458316714101085920],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
def witness_101 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal025.polynomial_8, 82800, by norm_num, R7.Core.Certificates.Terminal025.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal025.polynomial_9, 584236800, by norm_num, R7.Core.Certificates.Terminal025.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal025.polynomial_10, 248832, by norm_num, R7.Core.Certificates.Terminal025.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal025.polynomial_11, 53747712000, by norm_num, R7.Core.Certificates.Terminal025.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal025.polynomial_12, 623043477504000000, by norm_num, R7.Core.Certificates.Terminal025.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal025.polynomial_13, 73725005581516800000000, by norm_num, R7.Core.Certificates.Terminal025.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal025.polynomial_14, 16447679766328463704719360000000000, by norm_num, R7.Core.Certificates.Terminal025.positive_14⟩
theorem bound_101 : minorBindings polynomial_101 witness_101 := by
 decide +kernel
theorem positive_101 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_101 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_101 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry016
