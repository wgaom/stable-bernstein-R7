import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal076
import R7.Certificates.Spectral.Terminal.Terminal077

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL014
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_84 : BiPoly := [[72970153129131408],[-3794362934040000],[765950598691979904],[-47817593134380000],[2647733611395139200],[-45351732242520000],[3790891195784305920],[18078319450620000],[2375576767904190480],[11137659764400000],[560398128197948928],[0],[1029587752073664]]
def witness_84 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal076.polynomial_4, 7297015312913140800, by norm_num, R7.Core.Certificates.Terminal076.positive_4⟩
 | 1 => ⟨R7.Core.Certificates.Terminal076.polynomial_5, 547701025288667755212890822050003353600, by norm_num, R7.Core.Certificates.Terminal076.positive_5⟩
 | 2 => ⟨R7.Core.Certificates.Terminal076.polynomial_6, 144931586178363235014843293687224753660111659830537220784128, by norm_num, R7.Core.Certificates.Terminal076.positive_6⟩
 | 3 => ⟨R7.Core.Certificates.Terminal076.polynomial_7, 54939171152698055577306578022297513042719994106142907646207388845829863243776000, by norm_num, R7.Core.Certificates.Terminal076.positive_7⟩
 | 4 => ⟨R7.Core.Certificates.Terminal076.polynomial_8, 13051103445432252661008053651315255700487174668203839699825909740508992868631312888384609845248000000, by norm_num, R7.Core.Certificates.Terminal076.positive_8⟩
 | 5 => ⟨R7.Core.Certificates.Terminal076.polynomial_9, 731364356511523132695995635016961065172568244588011708765223574377128185101334980866641117231509481152508749414400000000, by norm_num, R7.Core.Certificates.Terminal076.positive_9⟩
 | 6 => ⟨R7.Core.Certificates.Terminal076.polynomial_10, 75300378376750088824653268530584324742043945091682920854659653023483363769724014577675277971171856152623976688952181694566236160000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_10⟩
theorem bound_84 : minorBindings polynomial_84 witness_84 := by
 decide +kernel
theorem positive_84 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_84 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_84 ρ hρ u
def polynomial_85 : BiPoly := [[15282078074496],[1242429794100000],[26756542341136656],[47088461074410000],[318388891098358080],[92410195722255000],[914756507645744700],[-99036875272500],[962179872704170920],[-21718436540580000],[367761271629903984],[0],[1029587752073664]]
def witness_85 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal076.polynomial_11, 1528207807449600, by norm_num, R7.Core.Certificates.Terminal076.positive_11⟩
 | 1 => ⟨R7.Core.Certificates.Terminal076.polynomial_12, 148097093627500979160546388684800, by norm_num, R7.Core.Certificates.Terminal076.positive_12⟩
 | 2 => ⟨R7.Core.Certificates.Terminal076.polynomial_13, 2193534807468464677223751431592002218404369210335232, by norm_num, R7.Core.Certificates.Terminal076.positive_13⟩
 | 3 => ⟨R7.Core.Certificates.Terminal076.polynomial_14, 197493282744155760358859079397644240043458293917484188564378528727040000, by norm_num, R7.Core.Certificates.Terminal076.positive_14⟩
 | 4 => ⟨R7.Core.Certificates.Terminal076.polynomial_15, 19002406111282929247639864546394472958888104524005526950088979796736258792695690567680000000, by norm_num, R7.Core.Certificates.Terminal076.positive_15⟩
 | 5 => ⟨R7.Core.Certificates.Terminal076.polynomial_16, 698602014295143506784219575483111927020360895728059437156686322142310550351903324950088650868645363712000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_16⟩
 | 6 => ⟨R7.Core.Certificates.Terminal076.polynomial_17, 71927207749227048644839883307980427371366938985338698424744971256235948485699011763780989277768475768704834749648076800000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_17⟩
theorem bound_85 : minorBindings polynomial_85 witness_85 := by
 decide +kernel
theorem positive_85 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_85 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_85 ρ hρ u
def polynomial_86 : BiPoly := [[2315304876957712],[14716860350960000],[268414299648775456],[434348399949360000],[3061817468484214260],[869840169330510000],[8991791495277235560],[-1661679792135000],[9791482781892008520],[-221639429311560000],[3887762014373270688],[0],[11325465272810304]]
def witness_86 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal076.polynomial_18, 231530487695771200, by norm_num, R7.Core.Certificates.Terminal076.positive_18⟩
 | 1 => ⟨R7.Core.Certificates.Terminal076.polynomial_19, 5548852236341439029288980656063385600, by norm_num, R7.Core.Certificates.Terminal076.positive_19⟩
 | 2 => ⟨R7.Core.Certificates.Terminal076.polynomial_20, 1596440467568656843053423932175997486348833936893123756032, by norm_num, R7.Core.Certificates.Terminal076.positive_20⟩
 | 3 => ⟨R7.Core.Certificates.Terminal076.polynomial_21, 1424990023815373927379765000039581707925525999933082049073137350849283489792000, by norm_num, R7.Core.Certificates.Terminal076.positive_21⟩
 | 4 => ⟨R7.Core.Certificates.Terminal076.polynomial_22, 1395276517235464043166499123465764865717186284851066036157497019853558296355518824672771702784000000, by norm_num, R7.Core.Certificates.Terminal076.positive_22⟩
 | 5 => ⟨R7.Core.Certificates.Terminal076.polynomial_23, 542275301170204533876164697332672829986736332422458135462237983197408442857538132235695932461388624183583519539200000000, by norm_num, R7.Core.Certificates.Terminal076.positive_23⟩
 | 6 => ⟨R7.Core.Certificates.Terminal076.polynomial_24, 614152009170590025519087224281156892586019667830076964315869546309916212671943741093235258054622770094422755078319750287909191680000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_24⟩
theorem bound_86 : minorBindings polynomial_86 witness_86 := by
 decide +kernel
theorem positive_86 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_86 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_86 ρ hρ u
def polynomial_87 : BiPoly := [[23986871534789820],[95273680958675000],[1439048666971522220],[1949246765003452500],[14793118897282357845],[3808001864958075000],[42858908415929020500],[-20583599553000000],[47093918658499667880],[-1008515091666420000],[19000999034211705840],[0],[56627326364051520]]
def witness_87 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal076.polynomial_25, 2398687153478982000, by norm_num, R7.Core.Certificates.Terminal076.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal076.polynomial_26, 315586414259634650940352155903543920000, by norm_num, R7.Core.Certificates.Terminal076.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal076.polynomial_27, 445110023321578032096616881170031557048747313885845625296000, by norm_num, R7.Core.Certificates.Terminal076.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal076.polynomial_28, 1896252272065489611439592900175306732099069983093970256229641604782530256800000000, by norm_num, R7.Core.Certificates.Terminal076.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal076.polynomial_29, 8930194554199112270829128616601429587517637161087770282207764349575140881513507691725111158400000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_29⟩
 | 5 => ⟨R7.Core.Certificates.Terminal076.polynomial_30, 16963440101748341879241577351134279652736942290101491435550630723554893473327913655860122251838660233519444505600000000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_30⟩
 | 6 => ⟨R7.Core.Certificates.Terminal076.polynomial_31, 96059425889874267902570395203445000554870985498871972947086246686754798347827084389334937799935632561442876413382874741932851200000000000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_31⟩
theorem bound_87 : minorBindings polynomial_87 witness_87 := by
 decide +kernel
theorem positive_87 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_87 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_87 ρ hρ u
def polynomial_88 : BiPoly := [[122250378583461320],[370249444115150000],[5096905013645031000],[5541735933406005000],[46437989835945606900],[10237410643428900000],[129895350185827893600],[-134817070625325000],[141239859614330474160],[-2706451322749200000],[56740310480042328960],[0],[169881979092154560]]
def witness_88 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal077.polynomial_0, 12225037858346132000, by norm_num, R7.Core.Certificates.Terminal077.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal077.polynomial_1, 5763654334547117865110976021019016000000, by norm_num, R7.Core.Certificates.Terminal077.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal077.polynomial_2, 25865962904850952602556731306051399198202147684731522000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal077.polynomial_3, 334476687560238139310770959374924776274254063570476505654375878078205920000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal077.polynomial_4, 4724142864201192325740645024878315019508777575429249178919887542121593657892805165793777720000000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal077.polynomial_5, 26798808283722130949000300468195016187114818965427336319201498456698507768057276101791090241828308906535877120000000000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal077.polynomial_6, 455263458854994147762408725499910103731840545698997228584313764805742194760217308554357618880845482842162224247231536020766720000000000000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_6⟩
theorem bound_88 : minorBindings polynomial_88 witness_88 := by
 decide +kernel
theorem positive_88 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_88 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_88 ρ hρ u
def polynomial_89 : BiPoly := [[398548752303384555],[924561960063675000],[12899377493419917100],[10866061078268782500],[103868722603334114955],[18640103362732125000],[276403477149777536100],[-504156353787900000],[292851652041279631440],[-4774714740998280000],[115056740695641389280],[0],[339763958184309120]]
def witness_89 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal077.polynomial_7, 39854875230338455500, by norm_num, R7.Core.Certificates.Terminal077.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal077.polynomial_8, 48245064848838145699088290275637326900000, by norm_num, R7.Core.Certificates.Terminal077.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal077.polynomial_9, 489788648137013233449170708422674972316068772670316474772000000, by norm_num, R7.Core.Certificates.Terminal077.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal077.polynomial_10, 13496021255381063136247954797513313232645627519460518136935122215426765676920000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal077.polynomial_11, 395232900833861472021856155316320264825515172587173755684297998060273848438783670433828671436480000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_11⟩
 | 5 => ⟨R7.Core.Certificates.Terminal077.polynomial_12, 4546651736176383747711406096339439336026986830250489840995830517996554113885853106616511620677701967722459727293440000000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_12⟩
 | 6 => ⟨R7.Core.Certificates.Terminal077.polynomial_13, 154478839036884930869044223036060849188837832557629879875059120045458090253612926347330334292420609717465221573401475840841390817280000000000000000000, by norm_num, R7.Core.Certificates.Terminal077.positive_13⟩
theorem bound_89 : minorBindings polynomial_89 witness_89 := by
 decide +kernel
theorem positive_89 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_89 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_89 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL014
