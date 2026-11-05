import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal019
import R7.Certificates.Spectral.Terminal.Terminal020

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry013
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_78 : BiPoly := [[407355289985936160,26955989540709193400,86928971940351854400],[0,107481204180206000,-29997208943655300000],[3044624420313169020,310119152354110445300,764394353025989536800],[0,-9378852821169054900,-124544488589637435000],[9052076070233652960,1219270104993796257000,2210543280144209516400],[0,-11078658750357225000,-176562306709363125000],[13705502652545272200,1989413391549046936500,2787112893174405948000],[0,7368188996151301500,-100127809940903550000],[11076728113660803120,1417229125570704573000,1546873549954677460800],[0,4882462576944847200,-18734572531045800000],[4459431059539862940,375997384109262324600,296351885338252464600],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_78 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_16, 92000, by norm_num, R7.Core.Certificates.Terminal019.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_17, 3680000, by norm_num, R7.Core.Certificates.Terminal019.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal019.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_19, 1440000000, by norm_num, R7.Core.Certificates.Terminal019.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_20, 19440000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_21, 3149280000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_22, 41820750385920000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_22⟩
theorem bound_78 : minorBindings polynomial_78 witness_78 := by
 decide +kernel
theorem positive_78 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_78 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_78 ρ hρ u
def polynomial_79 : BiPoly := [[23200958465792640,1425812403944553600,4616373850690737600],[0,234372094039416000,-1345895508565800000],[195616431597981960,19169496978673979400,47733144298489976400],[0,26436862613530200,-7118329585908870000],[657826737067377360,87575773651986072000,158821301454034712400],[0,-470001597073830000,-12897392641049250000],[1127106667731754800,163164854284702281000,228349569345756732000],[0,704373884929539000,-9014656160832300000],[1022016131492999040,130694070138059646000,142626799252672473600],[0,520567187465707200,-1997476391710800000],[455142800865089160,38375411624615264400,30246555072525224400],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
def witness_79 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_24, 2208000, by norm_num, R7.Core.Certificates.Terminal019.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_25, 1589760000, by norm_num, R7.Core.Certificates.Terminal019.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_26, 3456000, by norm_num, R7.Core.Certificates.Terminal019.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_27, 622080000000, by norm_num, R7.Core.Certificates.Terminal019.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_28, 5598720000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_29, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_30, 892176008232960000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_30⟩
theorem bound_79 : minorBindings polynomial_79 witness_79 := by
 decide +kernel
theorem positive_79 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_79 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_79 ρ hρ u
def polynomial_80 : BiPoly := [[99050245757807040,6343732302392132100,20601224537617533600],[0,402744528179586000,-8547366966999300000],[784822550869011960,79055588562374084400,195562190369831801400],[0,-2302948023375755700,-40149702367028955000],[2498926954742018640,336162900940575790500,609457391053045302600],[0,-3629631370536621000,-63031705074522225000],[4033554318532422000,585749869700004945000,820725388032910230000],[0,2861611599131077500,-38566193224416750000],[3438832967031771360,440174231761855014000,480501891101297462400],[0,1982159675350192800,-7605775491514200000],[1442899517636133720,121658219831227114800,95888015017154434800],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_80 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_0, 414000, by norm_num, R7.Core.Certificates.Terminal020.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_1, 298080000, by norm_num, R7.Core.Certificates.Terminal020.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_2, 279936000, by norm_num, R7.Core.Certificates.Terminal020.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_3, 83980800000000, by norm_num, R7.Core.Certificates.Terminal020.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_4, 188956800000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_5, 20407334400000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_6, 90332820833587200000000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_6⟩
theorem bound_80 : minorBindings polynomial_80 witness_80 := by
 decide +kernel
theorem positive_80 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_80 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_80 ρ hρ u
def polynomial_81 : BiPoly := [[157944986478665280,10476322483509074700,34105430508708175200],[0,-86970003452298000,-16461270244475100000],[1166628116156639400,119842948083641166000,295039062780293421000],[0,-5422711845072293100,-65922097598523765000],[3403184141299032720,460669760897906191500,835047165091281319800],[0,-5983103806325415000,-89729885854105875000],[5029069852468083600,731501833829827167000,1025578582234352874000],[0,3522706379980906500,-48646097123939550000],[3949841032778270880,505798782956683902000,552209504895937699200],[0,2256744565441994400,-8659389412416600000],[1539738411437216520,129823201027953766800,102323452266627886800],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_81 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_8, 414000, by norm_num, R7.Core.Certificates.Terminal020.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_9, 1490400000, by norm_num, R7.Core.Certificates.Terminal020.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_10, 11664000000, by norm_num, R7.Core.Certificates.Terminal020.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_11, 2099520000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_12, 4723920000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_13, 1530550080000000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_14, 6774961562519040000000000000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_14⟩
theorem bound_81 : minorBindings polynomial_81 witness_81 := by
 decide +kernel
theorem positive_81 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_81 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_81 ρ hρ u
def polynomial_82 : BiPoly := [[12849761611823616,841002739295060340,2735332752316285440],[0,10237277424092400,-1305704740830120000],[98279580694407804,10060268618872623060,24792494784419367360],[0,-468520663459210200,-5894441597633130000],[302437369828190520,40959848092519336500,74245087774398646800],[0,-584925794985175200,-8737123222589670000],[468578863386957960,68200517654590304700,95640206802855026400],[0,361010154347353800,-5008841796633660000],[381161753958454560,48826625310953109000,53312338444457750400],[0,240261778830326400,-921912180789600000],[152037063267699996,12819020478860843640,10103636481673319640],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
def witness_82 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_16, 82800, by norm_num, R7.Core.Certificates.Terminal020.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_17, 5961600, by norm_num, R7.Core.Certificates.Terminal020.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_18, 93312, by norm_num, R7.Core.Certificates.Terminal020.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_19, 5038848000, by norm_num, R7.Core.Certificates.Terminal020.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_20, 90699264000000, by norm_num, R7.Core.Certificates.Terminal020.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_21, 979552051200000000, by norm_num, R7.Core.Certificates.Terminal020.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_22, 433597540001218560000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_22⟩
theorem bound_82 : minorBindings polynomial_82 witness_82 := by
 decide +kernel
theorem positive_82 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_82 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_82 ρ hρ u
def polynomial_83 : BiPoly := [[39352394936209824,2622601796563945260,8614589314108124160],[0,-80317143973162800,-5022571827618360000],[284940079279470108,29561394130381153620,72651029719225014720],[0,-1725306591572173800,-19202659477171470000],[806499652875174720,109718311168816726500,198851104148098474800],[0,-1748731466980180800,-24775432065785430000],[1148275676211995880,167333991358628159100,234765301820199559200],[0,905466456495912600,-12689275730323320000],[864943980136493040,110838017402852436000,121033593083594433600],[0,554890298727182400,-2129178131823600000],[322473516357605724,27189387385099751160,21430006040746595160],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
def witness_83 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal020.polynomial_24, 82800, by norm_num, R7.Core.Certificates.Terminal020.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal020.polynomial_25, 5961600, by norm_num, R7.Core.Certificates.Terminal020.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal020.polynomial_26, 93312, by norm_num, R7.Core.Certificates.Terminal020.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal020.polynomial_27, 5038848000, by norm_num, R7.Core.Certificates.Terminal020.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal020.polynomial_28, 90699264000000, by norm_num, R7.Core.Certificates.Terminal020.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal020.polynomial_29, 8815968460800000000, by norm_num, R7.Core.Certificates.Terminal020.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal020.polynomial_30, 7804755720021934080000000000, by norm_num, R7.Core.Certificates.Terminal020.positive_30⟩
theorem bound_83 : minorBindings polynomial_83 witness_83 := by
 decide +kernel
theorem positive_83 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_83 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_83 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry013
