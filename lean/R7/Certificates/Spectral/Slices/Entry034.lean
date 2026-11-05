import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal051
import R7.Certificates.Spectral.Terminal.Terminal052

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry034
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_204 : BiPoly := [[4087929562156540800,204491280822969245125,653856630454915422000],[0,7675296406594565000,137784715766815500000],[46349572035722646600,3865245998416096824000,10052432855465440756500],[0,154388484539036341500,947858095071333225000],[212510621917323500400,26344517339700158778750,47851315765661964411000],[0,301381749048455280000,2330621159216069250000],[501705500981713596000,70697553089706660195000,97888767634707378390000],[0,-121320771289454205000,2347798459979668500000],[635367323713823870400,80396934242686413660000,87456583756939563936000],[0,-200618585323322544000,769796670959316000000],[400622503655079543600,33778527210858159324000,26623403901071670924000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
def witness_204 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_0, 57500, by norm_num, R7.Core.Certificates.Terminal051.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_1, 11500000, by norm_num, R7.Core.Certificates.Terminal051.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_2, 6000000, by norm_num, R7.Core.Certificates.Terminal051.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_3, 16200000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_4, 5103000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_5, 115736040000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_6, 215167760735558400000000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_6⟩
theorem bound_204 : minorBindings polynomial_204 witness_204 := by
 decide +kernel
theorem positive_204 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_204 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_204 ρ hρ u
def polynomial_205 : BiPoly := [[141056539504277760,5719953154326299900,16987408959795098400],[0,4274903465086129000,11343724195632300000],[1733575337588541600,118476605133332716500,325923872592807931500],[0,38252957800736666700,90657274214428605000],[8740473931622790000,994120429490374706250,1808835507703252350000],[0,70312948387481718000,261325655925315300000],[22868250512303674800,3116361891892541796000,4255294051480920282000],[0,-4819611637451016000,309634322362306200000],[32428069221388518720,4046129314932743388000,4382391377920142764800],[0,-30032722353790800000,115239022598700000000],[23183231175979222320,1954696498496360488800,1540643677523944408800],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
def witness_205 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_8, 46000, by norm_num, R7.Core.Certificates.Terminal051.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_9, 9200000, by norm_num, R7.Core.Certificates.Terminal051.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_10, 6000000, by norm_num, R7.Core.Certificates.Terminal051.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_11, 2160000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_12, 2177280000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_13, 29628426240000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_14, 3672196449886863360000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_14⟩
theorem bound_205 : minorBindings polynomial_205 witness_205 := by
 decide +kernel
theorem positive_205 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_205 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_205 ρ hρ u
def polynomial_206 : BiPoly := [[939143070888837120,40485115968314927550,121619993225829040800],[0,21712447000623215000,47695599526270500000],[11440026011766318480,826141643185283769700,2233514077196371400700],[0,175469556709040608500,374749167720559275000],[56742138456452633520,6601400037233588007750,12006854082521042266800],[0,302227442478342864000,1056204976652755650000],[145963174148083900800,20069596489416422391000,27510125575098446622000],[0,-14965454187078192000,1210540656458624400000],[203188534994776161600,25451640212389849080000,27600359866048990944000],[0,-111000941819610796800,425923427524795200000],[142353173887591716000,12002522359188178440000,9460092756725974440000],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
def witness_206 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_16, 69000, by norm_num, R7.Core.Certificates.Terminal051.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_17, 920000, by norm_num, R7.Core.Certificates.Terminal051.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal051.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_19, 8640000000, by norm_num, R7.Core.Certificates.Terminal051.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_20, 2351462400000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_21, 746636341248000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_22, 555236103222893740032000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_22⟩
theorem bound_206 : minorBindings polynomial_206 witness_206 := by
 decide +kernel
theorem positive_206 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_206 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_206 ρ hρ u
def polynomial_207 : BiPoly := [[2908547506812081600,135055904075425155875,417417805453269594000],[0,36695879243040655000,67582878887961000000],[34365119569749896400,2660811630779038883500,7053125294126364988500],[0,262639134667618456500,507364667861757975000],[165342611915836009200,19821821072293817006250,36030596491164111453000],[0,416109460244203080000,1363987758423168000000],[411551270947281483000,57248007763344321285000,78852181452216704595000],[0,-11710359260500792500,1462867331764592250000],[552684543239759112000,69565510048581495900000,75551265789966298080000],[0,-122533507203466464000,470175212202696000000],[372151868877561200400,31378022739020523636000,24731385349726476036000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
def witness_207 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal051.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_25, 34500000, by norm_num, R7.Core.Certificates.Terminal051.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal051.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_27, 16200000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_28, 6378750000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_29, 434010150000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_30, 806879102758344000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_30⟩
theorem bound_207 : minorBindings polynomial_207 witness_207 := by
 decide +kernel
theorem positive_207 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_207 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_207 ρ hρ u
def polynomial_208 : BiPoly := [[5260040661856449600,262750807073309691500,835402678421566464000],[0,0,0],[59797874371350978000,4963342027503320820000,12918002478608754270000],[0,0,0],[275289288078629714400,34036792302323219797500,61828095784746979296000],[0,0,0],[653092518383653860000,91923911209742218200000,127223189600294394900000],[0,0,0],[832105429026226185600,105235011618964975440000,114456925248687895104000],[0,0,0],[528740360153912088000,44580797334127519920000,35137487382125047920000],[0,0,0],[125701082923343558400,-529522964639532864000,631277859625592256000]]
def witness_208 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_0, 230000, by norm_num, R7.Core.Certificates.Terminal052.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_1, 405720000000, by norm_num, R7.Core.Certificates.Terminal052.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_2, 21168000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_3, 1143072000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_4, 760462940160000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_5, 4484297865535488000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_6, 11115826786522332675440640000000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_6⟩
theorem bound_208 : minorBindings polynomial_208 witness_208 := by
 decide +kernel
theorem positive_208 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_208 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_208 ρ hρ u
def polynomial_209 : BiPoly := [[257986726188001920,11662628252668013925,35328883173221872800],[0,4443868302682414000,6832213469686800000],[3119649999500346840,235355913892642810100,627871229708973803100],[0,30355341653415304200,51388672538636730000],[15260358330792131760,1809519374381231944500,3290173779705642608400],[0,45644298657948855000,136114004438404875000],[38679211305586438200,5360255406869398501500,7372121710327842888000],[0,-253309637362572000,140818844685852900000],[52952163665305302720,6656626133795809458000,7226592866144281324800],[0,-10451387379119198400,40103179864347600000],[36401740179827024520,3069216431849548486800,2419080862077070606800],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_209 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_8, 103500, by norm_num, R7.Core.Certificates.Terminal052.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal052.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal052.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_11, 4320000000, by norm_num, R7.Core.Certificates.Terminal052.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_12, 6531840000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_13, 14814213120000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_14, 2754147337415147520000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_14⟩
theorem bound_209 : minorBindings polynomial_209 witness_209 := by
 decide +kernel
theorem positive_209 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_209 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_209 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry034
