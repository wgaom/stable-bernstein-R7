import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal063
import R7.Certificates.Spectral.Terminal.Terminal064

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL004
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_24 : BiPoly := [[145940306258262816],[6775648096500000],[1244669722874467344],[71726389701570000],[3706827055953194880],[59781828865140000],[4738613994730382400],[-21554919344970000],[2714944877604789120],[-12251425740840000],[595423011210320736],[0],[1029587752073664]]
def witness_24 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_0, 14594030625826281600, by norm_num, R7.Core.Certificates.Terminal063.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_1, 1780030535839712329437414159662510899200, by norm_num, R7.Core.Certificates.Terminal063.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_2, 659452887628827296913494084110095099098215637839920004128768, by norm_num, R7.Core.Certificates.Terminal063.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_3, 312473364237076798597330369963136219869998044098752079584183321459497148088320000, by norm_num, R7.Core.Certificates.Terminal063.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_4, 84834029983825485962072212669156142480353844688167764464254894644684589487957899732402745507840000000, by norm_num, R7.Core.Certificates.Terminal063.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_5, 5051096104983216016885384122016313645859768962956866218088806323985236131084888162172625705905863532630480257024000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_6, 520054668423770932003290030451111500993189336221874518333405043256463677844291575842296233805931545817964434577741406770141593600000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_6⟩
theorem bound_24 : minorBindings polynomial_24 witness_24 := by
 decide +kernel
theorem positive_24 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_24 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_24 ρ hρ u
def polynomial_25 : BiPoly := [[4462506895095968],[14855877784480000],[206831243756865488],[263273728942020000],[1878449722323654120],[466473197598840000],[4994040581984896380],[-1876820981805000],[5150267473221453240],[-109149065691120000],[1978905890199007152],[0],[5662732636405152]]
def witness_25 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_7, 446250689509596800, by norm_num, R7.Core.Certificates.Terminal063.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_8, 8493518581717097837644130546093363200, by norm_num, R7.Core.Certificates.Terminal063.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_9, 1521314906401684534894073205000167506176251249426632761344, by norm_num, R7.Core.Certificates.Terminal063.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_10, 755130422465087535307988617929007514604646051969848986424861373510110953472000, by norm_num, R7.Core.Certificates.Terminal063.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_11, 388912351889275644421975301282293701282143916396992775680461646408728725284546697263722364928000000, by norm_num, R7.Core.Certificates.Terminal063.positive_11⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_12, 76939603741760915112944976783748145851136882710446814477262148302641317799234552739131063834021998772110596505600000000, by norm_num, R7.Core.Certificates.Terminal063.positive_12⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_13, 43568840514054948445448106438543282314960995221563112478653259489993070921288493280373614696568008836326428228020682915703685120000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_13⟩
theorem bound_25 : minorBindings polynomial_25 witness_25 := by
 decide +kernel
theorem positive_25 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_25 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_25 ρ hρ u
def polynomial_26 : BiPoly := [[55361079041650960],[161306888533100000],[2084022294914971600],[2352912516976470000],[17972359507574106060],[4089137622584850000],[47576624381796854700],[-28951448238900000],[49576404301148766240],[-990137953055160000],[19351247864335423920],[0],[56627326364051520]]
def witness_26 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_14, 5536107904165096000, by norm_num, R7.Core.Certificates.Terminal063.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_15, 1065612704614260718020198213024812800000, by norm_num, R7.Core.Certificates.Terminal063.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_16, 1841602838082346188671031707948644429810794385263774592000000, by norm_num, R7.Core.Certificates.Terminal063.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_17, 8717179249836856078216248580798002003756145170157377727090627987537578240000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_18, 43216636426533742598570935785545044468949620991291019207078556649134224200450257560547061760000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_18⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_19, 83608219113721027988879530235460629478615911560650436200378087708388334496899143563084272730870977776642129920000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_19⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_20, 473450991046981097782459862868442190475619331457905112260137478333016655708504371553214317824298649826479945978698181341347840000000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_20⟩
theorem bound_26 : minorBindings polynomial_26 witness_26 := by
 decide +kernel
theorem positive_26 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_26 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_26 ρ hρ u
def polynomial_27 : BiPoly := [[355586004721084940],[848531412531150000],[10664095510191059700],[9947411646553380000],[83935498079834693085],[16465287019640850000],[215968058656698555900],[-228375133081425000],[223003012585217841360],[-3969461940032160000],[86686585455620224800],[0],[254822968638231840]]
def witness_27 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_21, 35558600472108494000, by norm_num, R7.Core.Certificates.Terminal063.positive_21⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_22, 35361616645912137232290218222396996400000, by norm_num, R7.Core.Certificates.Terminal063.positive_22⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_23, 288344305027427208325572466854351489975364465618323064446000000, by norm_num, R7.Core.Certificates.Terminal063.positive_23⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_24, 6203349140629227057196629695593727300610086708546214656357114604187583353140000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_24⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_25, 138336517051185719926823616053672759265328928847216821198365449502939688647023740269144490912040000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_25⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_26, 1198947671035692067919156390938996786251299875029724789955095910266514279119730420526730468429961071149137222659200000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_26⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_27, 30551940477520926483004146977669162265177307465635738083152543396542921980554243186736870789810193632479828328517896053587090892800000000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_27⟩
theorem bound_27 : minorBindings polynomial_27 witness_27 := by
 decide +kernel
theorem positive_27 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_27 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_27 ρ hρ u
def polynomial_28 : BiPoly := [[1402443455171490580],[2672186246729625000],[35081108689767730880],[25747058019712740000],[248564183566323641400],[39817900756778400000],[611483094295925245200],[-1042830083405137500],[616022736130022640480],[-9288808243509600000],[234316467352767395520],[0],[679527916368618240]]
def witness_28 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_28, 140244345517149058000, by norm_num, R7.Core.Certificates.Terminal063.positive_28⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_29, 464301410221792300587245615010609581920000, by norm_num, R7.Core.Certificates.Terminal063.positive_29⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_30, 11316283335122571166017153994486617346183002795465449741087744000, by norm_num, R7.Core.Certificates.Terminal063.positive_30⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_31, 690131260624471821830272997958185325172477491805738107031774642632472315791482880000000, by norm_num, R7.Core.Certificates.Terminal063.positive_31⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_0, 42513623979882826413644711771848557533881330103162368176773598896111120311894494379369615194831498240000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_0⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_1, 996015353840886331747412657804713681207690176831868049463126012826264953256548423520670236739322924234505212386426388480000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_1⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_2, 67682023806664951135100872139884560124144588990693060548771491464655154949649497643119757724766280824333177738706236911193150289105387520000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_2⟩
theorem bound_28 : minorBindings polynomial_28 witness_28 := by
 decide +kernel
theorem positive_28 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_28 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_28 ρ hρ u
def polynomial_29 : BiPoly := [[3783954436662442855],[5414723055778225000],[80621568388176022390],[44382349396965990000],[512000711312030462685],[63320277294598950000],[1189731360645749754900],[-2942991064334475000],[1153930040936907529680],[-14127007645164960000],[422925462374389581600],[0],[1189173853645081920]]
def witness_29 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal064.polynomial_3, 378395443666244285500, by norm_num, R7.Core.Certificates.Terminal064.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal064.polynomial_4, 2916371681225666778917944606258277629810000, by norm_num, R7.Core.Certificates.Terminal064.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal064.polynomial_5, 147500555311507221980511601023713739316054218879013957872548938000, by norm_num, R7.Core.Certificates.Terminal064.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal064.polynomial_6, 17519370965779618552222445459711585253826357121635436866641992883736644402675529620000000, by norm_num, R7.Core.Certificates.Terminal064.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_7, 2021609651744896036441315977519413726405620069858928744747684937539367651118501213055313929362146287160000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_7⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_8, 85490278715607184673947251621821424072035305171585738713345731265902013249268897942027935256022259106611800618874105225600000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_8⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_9, 10166280418943072016839941858514634879661685154044819199347306354439865856490224603748894968276596048416442318444492927093468227401208115200000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_9⟩
theorem bound_29 : minorBindings polynomial_29 witness_29 := by
 decide +kernel
theorem positive_29 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_29 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_29 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL004
