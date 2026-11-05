import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal034
import R7.Certificates.Spectral.Terminal.Terminal035

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry023
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_138 : BiPoly := [[2100876533896069440,120335075857622138100,394332312219577149600],[0,40051792942527966000,-16239599024793300000],[20852397365081265720,1941978677929432678300,4904675811551466739800],[0,145204107249585266400,-122064852238526340000],[82736138211158391120,10752901693605007666500,19512373281000079825800],[0,126937986621777801000,-320017809956006025000],[167289519853515961800,23990129276507488903500,33452196636118869612000],[0,52313302108182528000,-327399994535304600000],[179849707598550790080,22914200049536755512000,24978431955160886227200],[0,29071675238469494400,-111551373875541600000],[95579988181668723600,8058836441169205524000,6351776565230297124000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_138 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_16, 966000, by norm_num, R7.Core.Certificates.Terminal034.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_17, 5520000, by norm_num, R7.Core.Certificates.Terminal034.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal034.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_19, 1440000000, by norm_num, R7.Core.Certificates.Terminal034.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_20, 2903040000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_21, 65840947200000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_22, 24481309665912422400000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_22⟩
theorem bound_138 : minorBindings polynomial_138 witness_138 := by
 decide +kernel
theorem positive_138 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_138 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_138 ρ hρ u
def polynomial_139 : BiPoly := [[3139863045703937280,195255740526421099700,631247574752445655200],[0,25223303719525354000,-87036480601247700000],[29311040413336172400,2871907863619930681000,7149041990152410703500],[0,45797080046451210900,-503738933347378665000],[109268483272875944640,14490711243424468458000,26282483948365775517600],[0,9860017885644915000,-983624694658331625000],[206672457657229333200,29838543891934143811500,41717578933591452063000],[0,68236078587033388500,-755245347209491950000],[207117433074040231680,26448239861419313952000,28850638109292968371200],[0,49734188217877564800,-190835821423447200000],[102494285199066035520,8641816098615488476800,6811266784842701596800],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_139 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal034.polynomial_24, 322000, by norm_num, R7.Core.Certificates.Terminal034.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal034.polynomial_25, 27600000, by norm_num, R7.Core.Certificates.Terminal034.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal034.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal034.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal034.polynomial_27, 180000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal034.polynomial_28, 5670000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal034.polynomial_29, 925888320000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal034.polynomial_30, 344268417176893440000000000000000000, by norm_num, R7.Core.Certificates.Terminal034.positive_30⟩
theorem bound_139 : minorBindings polynomial_139 witness_139 := by
 decide +kernel
theorem positive_139 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_139 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_139 ρ hρ u
def polynomial_140 : BiPoly := [[132066994343742720,7308704268378002800,24065203942394044800],[0,3204064574543298000,-510236507799900000],[1332391437711555840,121614773058648835100,308874952748047800600],[0,11902877821274035200,-5898047401855620000],[5415360042916892880,698885968533880836000,1268470307124780109200],[0,10243102115410029000,-20021977786988475000],[11216713817706118200,1605720934764184486500,2237541360809379588000],[0,4008386744077158000,-25543025849145600000],[12352153982675631840,1573313274700767126000,1714899025272779625600],[0,2591394900241377600,-9943481378516400000],[6710935340415038040,565833196933156983600,445975801388510223600],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_140 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_0, 184000, by norm_num, R7.Core.Certificates.Terminal035.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_1, 7360000, by norm_num, R7.Core.Certificates.Terminal035.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal035.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_3, 33120000000, by norm_num, R7.Core.Certificates.Terminal035.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_4, 622080000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_5, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_6, 16059168148193280000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_6⟩
theorem bound_140 : minorBindings polynomial_140 witness_140 := by
 decide +kernel
theorem positive_140 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_140 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_140 ρ hρ u
def polynomial_141 : BiPoly := [[681751241071752960,40282031807757970400,131225137197221366400],[0,11049223783198944000,-26388935730052200000],[6685525433328620400,636240797520344311000,1596989144295764586000],[0,26108831664107180400,-159367735170214740000],[26137920568181798880,3432073730719030716000,6226392097375847899200],[0,11347954010711586000,-338983838621485650000],[51921284313023730000,7477236099649335105000,10443489774481222200000],[0,26728574171552946000,-286725667374907200000],[54610845583630006080,6970067480008362672000,7602011172724155667200],[0,20525220534362169600,-78757640587454400000],[28238221432395744480,2380908516965491723200,1876573501946458603200],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
def witness_141 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_8, 368000, by norm_num, R7.Core.Certificates.Terminal035.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_9, 147200000, by norm_num, R7.Core.Certificates.Terminal035.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_10, 16000000, by norm_num, R7.Core.Certificates.Terminal035.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_11, 1656000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_12, 178848000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_13, 56324242944000000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_14, 5983646052016816128000000000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_14⟩
theorem bound_141 : minorBindings polynomial_141 witness_141 := by
 decide +kernel
theorem positive_141 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_141 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_141 ρ hρ u
def polynomial_142 : BiPoly := [[1496461821043625280,94194010889176357200,305083081077925075200],[0,10445274162051354000,-93998471898647700000],[13813348260190027320,1368593058524722827300,3398223184432189408800],[0,-7816987085890613400,-512145428526001710000],[50888906127252501840,6787973842737823458000,12309592275765468165600],[0,-35571041093613519000,-944800011321990525000],[94857182729231617800,13729061716844552473500,19212513466268590902000],[0,54172821211762491000,-685014884169451200000],[93330178040684445120,11930782958532068508000,13018727949047621740800],[0,42011488184045644800,-161202929898067200000],[45146292290064801360,3806514233913965162400,3000200845704523322400],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
def witness_142 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_16, 552000, by norm_num, R7.Core.Certificates.Terminal035.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_17, 198720000, by norm_num, R7.Core.Certificates.Terminal035.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_18, 3888000, by norm_num, R7.Core.Certificates.Terminal035.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_19, 349920000000, by norm_num, R7.Core.Certificates.Terminal035.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_20, 6298560000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_21, 12244400640000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_22, 1951188930005483520000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_22⟩
theorem bound_142 : minorBindings polynomial_142 witness_142 := by
 decide +kernel
theorem positive_142 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_142 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_142 ρ hρ u
def polynomial_143 : BiPoly := [[104404313096066880,6416155817750491200,20773682328108319200],[0,1160273658528087000,-6342115678613100000],[1005185639476377180,98252812850761660200,244809809699917246200],[0,575769005389777500,-36892910091625875000],[3826800120587003280,508575448412817261000,922362870781571920200],[0,-2284562555027118000,-74734970761877175000],[7371964169402873400,1066448557530241533000,1492101763215615756000],[0,4677950170849657500,-58909903919154000000],[7476634404569685600,955860232651707105000,1043053280544649104000],[0,3835607683469853600,-14717669457605400000],[3704087687891417100,312310530774794439000,246155474792359539000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_143 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal035.polynomial_24, 9936000, by norm_num, R7.Core.Certificates.Terminal035.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal035.polynomial_25, 33120000, by norm_num, R7.Core.Certificates.Terminal035.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal035.polynomial_26, 1296000, by norm_num, R7.Core.Certificates.Terminal035.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal035.polynomial_27, 5365440000000, by norm_num, R7.Core.Certificates.Terminal035.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal035.polynomial_28, 7873200000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal035.polynomial_29, 19131876000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal035.polynomial_30, 254061058594464000000000000000000, by norm_num, R7.Core.Certificates.Terminal035.positive_30⟩
theorem bound_143 : minorBindings polynomial_143 witness_143 := by
 decide +kernel
theorem positive_143 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_143 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_143 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry023
