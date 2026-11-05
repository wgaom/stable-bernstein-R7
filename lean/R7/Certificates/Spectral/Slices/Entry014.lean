import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal021
import R7.Certificates.Spectral.Terminal.Terminal022

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry014
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_84 : BiPoly := [[4818660604433856,323927101321615440,1068955738507607040],[0,-16464440254046400,-675794015779680000],[33938272470011328,3545659183910641920,8701551806328299520],[0,-228506532384175200,-2419675978097880000],[91647687826724400,12501538741144980000,22655639340672696000],[0,-211601031271819200,-2916056153308320000],[123581238695461440,18024267946188700800,25295471821335369600],[0,98992054936101600,-1396442533398120000],[87960404759643360,11274798562163514000,12312955388933942400],[0,57205185435792000,-219502900188000000],[30988446016346496,2612793982952528640,2059339919831504640],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
def witness_84 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_0, 8942400, by norm_num, R7.Core.Certificates.Terminal021.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_1, 1514341785600, by norm_num, R7.Core.Certificates.Terminal021.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_2, 139314069504, by norm_num, R7.Core.Certificates.Terminal021.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_3, 361102068154368000, by norm_num, R7.Core.Certificates.Terminal021.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_4, 19499511680335872000000, by norm_num, R7.Core.Certificates.Terminal021.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_5, 6739031236724077363200000000, by norm_num, R7.Core.Certificates.Terminal021.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_6, 542368016381532504714117120000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_6⟩
theorem bound_84 : minorBindings polynomial_84 witness_84 := by
 decide +kernel
theorem positive_84 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_84 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_84 ρ hρ u
def polynomial_85 : BiPoly := [[317278064489472,-2126945970126720,8582142896772480],[0,5416157092356000,105138593287200000],[3770919163334592,105844395827756880,451714058526158280],[0,229955636259896400,730710772395660000],[16292922280306560,1469402662266792000,2671618533500840400],[0,449649281386999800,1693614323077830000],[34328121859850400,4323051783673015500,5675183447198436000],[0,-11411149897095300,1543482320988960000],[37697316325561440,4554540400842441000,4882766712667689600],[0,-111550111599794400,428030655366600000],[20336167698227388,1714646051312596920,1351441822389424920],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
def witness_85 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_8, 2649600, by norm_num, R7.Core.Certificates.Terminal021.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_9, 572313600, by norm_num, R7.Core.Certificates.Terminal021.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_10, 6718464, by norm_num, R7.Core.Certificates.Terminal021.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_11, 1813985280000, by norm_num, R7.Core.Certificates.Terminal021.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_12, 1689727288320000000, by norm_num, R7.Core.Certificates.Terminal021.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_13, 2380311484416000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_14, 191571276764174745600000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_14⟩
theorem bound_85 : minorBindings polynomial_85 witness_85 := by
 decide +kernel
theorem positive_85 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_85 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_85 ρ hρ u
def polynomial_86 : BiPoly := [[3014141612649984,-9600963989713840,110799436055338560],[0,66473440976713600,945896234332320000],[35195245524456192,1080104662396270880,4383368501480477280],[0,2121839437821974400,6669716100381360000],[154782761662912320,14142814452164026500,25716045985634233800],[0,4232533028320479600,15957755353844910000],[336415594226533920,42500265119721779400,55886303473642297800],[0,-115152546330271800,15114355005736260000],[383256049309874640,46350746762864661000,49707163940172177600],[0,-1138383190172260800,4368107713741200000],[214982344238403816,18126258256733167440,14286670693831063440],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
def witness_86 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_16, 36800, by norm_num, R7.Core.Certificates.Terminal021.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_17, 2355200, by norm_num, R7.Core.Certificates.Terminal021.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_18, 65536, by norm_num, R7.Core.Certificates.Terminal021.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_19, 2359296000, by norm_num, R7.Core.Certificates.Terminal021.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_20, 63700992000000, by norm_num, R7.Core.Certificates.Terminal021.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_21, 4127824281600000000, by norm_num, R7.Core.Certificates.Terminal021.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_22, 3654352929722204160000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_22⟩
theorem bound_86 : minorBindings polynomial_86 witness_86 := by
 decide +kernel
theorem positive_86 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_86 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_86 ρ hρ u
def polynomial_87 : BiPoly := [[14277512902026240,17836086054365100,741973101721761600],[0,445457386858783000,4185847663644600000],[164453974623203040,5958986327290383100,22179913819058861100],[0,9529967617513208100,29232029383918515000],[723677297950283040,68485494048159143625,124546691165013161100],[0,18529587619587567000,70229317543642575000],[1587675636018081000,202667242700569792500,267936438299112540000],[0,-578424071584800000,67398048057678750000],[1836697023195410160,222971141345497569000,239410399145696654400],[0,-5179929541210965600,19875987612023400000],[1050701997741748380,88590045984484174200,69824494156786954200],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_87 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal021.polynomial_24, 414000, by norm_num, R7.Core.Certificates.Terminal021.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal021.polynomial_25, 1840000, by norm_num, R7.Core.Certificates.Terminal021.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal021.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal021.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal021.polynomial_27, 21600000000, by norm_num, R7.Core.Certificates.Terminal021.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal021.polynomial_28, 777600000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal021.polynomial_29, 41990400000000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal021.polynomial_30, 185870001715200000000000000000, by norm_num, R7.Core.Certificates.Terminal021.positive_30⟩
theorem bound_87 : minorBindings polynomial_87 witness_87 := by
 decide +kernel
theorem positive_87 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_87 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_87 ρ hρ u
def polynomial_88 : BiPoly := [[44022331447914240,289572006163642600,3136987401429681600],[0,1765810758988294000,11928841936192800000],[497551834051092000,21694831106613675000,74045319912264780000],[0,27120038452283260200,81270596640015630000],[2168995278565810800,215645917730427862500,392191378672572972000],[0,49810235164190244000,191759907968109900000],[4737280816659355200,614670757889978124000,819316496263793418000],[0,-1950922532218401000,181775469690088200000],[5474488048612089120,668913413607804798000,719730015150504700800],[0,-13900860060897456000,53339204745684000000],[3137580159155082720,264545390773943524800,208508166882939844800],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_88 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_0, 92000, by norm_num, R7.Core.Certificates.Terminal022.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_1, 184000000, by norm_num, R7.Core.Certificates.Terminal022.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_2, 6000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_3, 2160000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_4, 9720000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_5, 7822811520000000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_6, 103882743958625280000000000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_6⟩
theorem bound_88 : minorBindings polynomial_88 witness_88 := by
 decide +kernel
theorem positive_88 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_88 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_88 ρ hρ u
def polynomial_89 : BiPoly := [[97265556645053760,1264779696740186775,9082228384839938400],[0,4456994742202503000,24233911495946100000],[1074319157470844700,56189499920441790500,177490767123798273000],[0,53217262712705181300,158903721053432595000],[4598677313616526560,483962185178509116375,880029519042266577900],[0,90657020577385665000,361573394230949625000],[9886499095636915200,1309082783402112196500,1762086677856459318000],[0,-4826366001651852000,330844296459911400000],[11258931809234350080,1387485980046584082000,1496952646677208627200],[0,-24523862996324030400,94100893310595600000],[6362315322731139960,536439264624941036400,422808227290405796400],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_89 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_8, 34500, by norm_num, R7.Core.Certificates.Terminal022.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_9, 6900000, by norm_num, R7.Core.Certificates.Terminal022.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal022.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_11, 180000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_12, 38880000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_13, 37791360000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_14, 1003698009262080000000000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_14⟩
theorem bound_89 : minorBindings polynomial_89 witness_89 := by
 decide +kernel
theorem positive_89 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_89 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_89 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry014
