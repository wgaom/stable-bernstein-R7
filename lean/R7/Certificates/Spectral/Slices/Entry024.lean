import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal036
import R7.Certificates.Spectral.Terminal.Terminal037

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry024
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_144 : BiPoly := [[445726105910131680,28546795360764594450,92705510419278901200],[0,2022889882344678000,-40634658575568900000],[4037240329245097560,406042655594530028400,1004797024937310942900],[0,-11555226653436246600,-214141104491407290000],[14565872518594064640,1957461616163825894250,3548948930109769130100],[0,-21112193029910733000,-378648228415687425000],[26466981953944658400,3841979806746259240500,5382397328836680531000],[0,19446337817729892000,-260496850456758150000],[25238353279963384080,3230066554322105097000,3525842844781074187200],[0,14982038065633924800,-57487809559237200000],[11765925596831560200,992045215402288218000,781905625811024418000],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
def witness_144 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_0, 1863000, by norm_num, R7.Core.Certificates.Terminal036.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_1, 74520000, by norm_num, R7.Core.Certificates.Terminal036.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_2, 34992000, by norm_num, R7.Core.Certificates.Terminal036.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_3, 9447840000000, by norm_num, R7.Core.Certificates.Terminal036.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_4, 3061100160000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_5, 401677562995200000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_6, 16002188212207471718400000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_6⟩
theorem bound_144 : minorBindings polynomial_144 witness_144 := by
 decide +kernel
theorem positive_144 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_144 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_144 ρ hρ u
def polynomial_145 : BiPoly := [[64248808059118080,4205013696475301700,13676663761581427200],[0,62773198789455000,-6915885568366500000],[562102637784562620,57480763626308341800,141684957863874460800],[0,-2759751147004647300,-35289275411992995000],[1961260519491902160,265466320787688889500,481201027541646944400],[0,-3930077599415568000,-59232393838415925000],[3424230155520077400,498290437877977098000,698721040891834866000],[0,2762091680323423500,-38251554350672700000],[3116311482913079040,399172490076565431000,435836205325355673600],[0,2050805897873143200,-7869178971739800000],[1379954236665429900,116350982053354791000,91704980804996691000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_145 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_8, 414000, by norm_num, R7.Core.Certificates.Terminal036.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_9, 149040000, by norm_num, R7.Core.Certificates.Terminal036.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_10, 11664000, by norm_num, R7.Core.Certificates.Terminal036.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_11, 2099520000000, by norm_num, R7.Core.Certificates.Terminal036.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_12, 14171760000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_13, 11479125600000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_14, 50812211718892800000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_14⟩
theorem bound_145 : minorBindings polynomial_145 witness_145 := by
 decide +kernel
theorem positive_145 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_145 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_145 ρ hρ u
def polynomial_146 : BiPoly := [[1031153709590784,8994959686823160,71795582218510560],[0,40132433449154400,262319825339280000],[11312757490003776,455868639489080640,1606198108432974840],[0,653247157874101200,1966755654219780000],[52951997410996320,5050792393311327750,9186265109942106300],[0,1402657447223721600,5306875476911235000],[127014050881446480,16196828059179498600,21402437291280650700],[0,-47206170627359400,5693226977725830000],[160213594383636120,19426175735030140500,20850312070913680800],[0,-480523557660652800,1843824361579200000],[98775671677104456,8328280820661185040,6564145994462921040],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
def witness_146 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal036.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_17, 2649600, by norm_num, R7.Core.Certificates.Terminal036.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_18, 27648, by norm_num, R7.Core.Certificates.Terminal036.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_19, 1492992000, by norm_num, R7.Core.Certificates.Terminal036.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_20, 241864704000000, by norm_num, R7.Core.Certificates.Terminal036.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_21, 15672832819200000000, by norm_num, R7.Core.Certificates.Terminal036.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_22, 6937560640019496960000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_22⟩
theorem bound_146 : minorBindings polynomial_146 witness_146 := by
 decide +kernel
theorem positive_146 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_146 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_146 ρ hρ u
def polynomial_147 : BiPoly := [[8725146773460480,93085899273697700,611959221694243200],[0,369740863730269000,2165381835787800000],[99510366810218400,4216830420768798500,14461188934862218500],[0,5620195226885202300,16547423137891245000],[473852489652249120,45937722250482655875,83565718155467358300],[0,12040355747135475000,45506426148360000000],[1158574112769951000,148551205582320547500,196858465120667340000],[0,-435768182439349500,50178050549865900000],[1499515471616777280,182187055072551447000,195671061187673875200],[0,-4384777463653456800,16824897299410200000],[953863103940665580,80425064787757522200,63389056907313502200],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_147 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal036.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal036.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal036.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal036.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal036.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal036.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal036.polynomial_27, 900000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal036.polynomial_28, 4050000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal036.polynomial_29, 218700000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal036.polynomial_30, 968072925600000000000000000000, by norm_num, R7.Core.Certificates.Terminal036.positive_30⟩
theorem bound_147 : minorBindings polynomial_147 witness_147 := by
 decide +kernel
theorem positive_147 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_147 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_147 ρ hρ u
def polynomial_148 : BiPoly := [[37875068948430720,580711510736792800,3076279104251464800],[0,1741264278881196000,8672119329670200000],[434179442556163440,20645275813752856600,67140471457357172100],[0,23080138164950604000,66153395076447600000],[2066146206671375640,207585924300744349875,377646773772702432600],[0,47607028962633810000,180962284736966625000],[5054815943862971400,656224535457049023000,875087683544455326000],[0,-1997512756671492000,199609335018396900000],[6576087403459051200,802932259073975235000,863729356315029408000],[0,-17607756077136777600,67562992677866400000],[4227017714417264220,356401429237118359800,280906835939516179800],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
def witness_148 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal037.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_1, 14720000, by norm_num, R7.Core.Certificates.Terminal037.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal037.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_3, 8640000000, by norm_num, R7.Core.Certificates.Terminal037.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_4, 1555200000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_5, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_6, 15055470138931200000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_6⟩
theorem bound_148 : minorBindings polynomial_148 witness_148 := by
 decide +kernel
theorem positive_148 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_148 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_148 ρ hρ u
def polynomial_149 : BiPoly := [[106486450394279040,2224722323617143350,10375390769667513600],[0,5135645782600087000,22134965623911900000],[1213764605698321800,66291735708193539500,203511826629617899500],[0,58544101234546700700,165550345723230705000],[5708632643962410960,601538633256863734500,1094170992565412111400],[0,113633023291724718000,441513185915940300000],[13799904987659860800,1823392312702130466000,2452400025702975522000],[0,-6102567581548464000,474865026976504800000],[17768001761447958720,2185743977292805668000,2356863503578800364800],[0,-41084764179985814400,157646982915021600000],[11330150574726687600,955302800017018284000,752946158188393884000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_149 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal037.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_9, 4600000, by norm_num, R7.Core.Certificates.Terminal037.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal037.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_11, 720000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_12, 311040000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_13, 3023308800000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_14, 160591681481932800000000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_14⟩
theorem bound_149 : minorBindings polynomial_149 witness_149 := by
 decide +kernel
theorem positive_149 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_149 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_149 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry024
