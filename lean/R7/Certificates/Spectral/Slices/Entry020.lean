import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal030
import R7.Certificates.Spectral.Terminal.Terminal031

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry020
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_120 : BiPoly := [[4281469181495118720,226762214659986459050,783338845725416884800],[0,84850446598246318000,439029998583636600000],[42457931085284079120,3843123083900416884300,9825431360152376508300],[0,582689520588974589000,2434646423184175350000],[167849685331718181120,21580356630640986744000,39160578709406432800800],[0,737159504142408102000,4656302719336462950000],[337531258186979058000,48189059363812898205000,67065320266619279220000],[0,-164988458570659374000,3562637743125316800000],[360930860863736587200,45895592011182772320000,50000468657454207648000],[0,-227287642773488774400,872128923026961600000],[191159976363337447200,16117672882338411048000,12703553130460594248000],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
def witness_120 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_0, 23000, by norm_num, R7.Core.Certificates.Terminal030.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_1, 920000, by norm_num, R7.Core.Certificates.Terminal030.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_2, 48000, by norm_num, R7.Core.Certificates.Terminal030.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_3, 43200000000, by norm_num, R7.Core.Certificates.Terminal030.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_4, 54432000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_5, 2469035520000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_6, 1836098224943431680000000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_6⟩
theorem bound_120 : minorBindings polynomial_120 witness_120 := by
 decide +kernel
theorem positive_120 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_120 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_120 ρ hρ u
def polynomial_121 : BiPoly := [[3328147747099408320,201382022743305055550,666781484296780948800],[0,25388231582981492000,293870239611485400000],[30974696624771218440,3016830430487036211600,7537017337959361247100],[0,216418264004439296100,1486325997875773215000],[114484255017859082160,15161689415959137195750,27497260147535359394400],[0,263026687238049627000,2580058370802718575000],[214164570253141683000,30906377964337023787500,43199209805407722720000],[0,-112298967320960070000,1789439723002449000000],[212101856010420022080,27080238045255358572000,29538560695365881107200],[0,-105234659127682963200,403797535185844800000],[103714455260959678800,8744694861694244292000,6892353294186067092000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_121 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal030.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal030.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_10, 432000, by norm_num, R7.Core.Certificates.Terminal030.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_11, 194400000000, by norm_num, R7.Core.Certificates.Terminal030.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_12, 97977600000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_13, 6666395904000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_14, 2478732603673632768000000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_14⟩
theorem bound_121 : minorBindings polynomial_121 witness_121 := by
 decide +kernel
theorem positive_121 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_121 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_121 ρ hρ u
def polynomial_122 : BiPoly := [[1629421159943744640,107823958162836773600,347715887761407417600],[0,-486960244635372000,126985763026758600000],[13986967663335224160,1424088173202100647400,3510336714053861399400],[0,44208506237170914600,591246313509438990000],[47282060457449637120,6365901859191401784000,11541600697763530090800],[0,58378293301917168000,937348396722679050000],[80602430126928739200,11696938365302293059000,16385648559071948478000],[0,-43658802873696087000,591830513676675900000],[72705557419899497280,9301295300830378992000,10151781800104870675200],[0,-31989139695694886400,122746021785129600000],[32421661644602521440,2733635704664083089600,2154584391123711729600],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
def witness_122 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_16, 368000, by norm_num, R7.Core.Certificates.Terminal030.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_17, 29440000, by norm_num, R7.Core.Certificates.Terminal030.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_18, 128000, by norm_num, R7.Core.Certificates.Terminal030.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_19, 23040000000, by norm_num, R7.Core.Certificates.Terminal030.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_20, 622080000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_21, 7255941120000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_22, 770840071113277440000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_22⟩
theorem bound_122 : minorBindings polynomial_122 witness_122 := by
 decide +kernel
theorem positive_122 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_122 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_122 ρ hρ u
def polynomial_123 : BiPoly := [[61076027414223360,1711265909995006400,7140670384238702400],[0,3260063155872785000,10139793421167000000],[688192747308563040,43920938988943538100,126511623361966323600],[0,27715395802889181900,70112684649434985000],[3107874924968476320,347195416378000074000,631547729611909993800],[0,45480960645248007000,172716761966435325000],[7217487621033546600,976084907061549829500,1327558788842639544000],[0,-2605240928291715000,173410108164738000000],[9022224373917704640,1121505163525518246000,1213286438972920377600],[0,-14295575840404420800,54853774756981200000],[5665075287363343800,477651400008509142000,376473079094196942000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_123 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal030.polynomial_24, 736000, by norm_num, R7.Core.Certificates.Terminal030.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal030.polynomial_25, 3680000, by norm_num, R7.Core.Certificates.Terminal030.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal030.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal030.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal030.polynomial_27, 4320000000, by norm_num, R7.Core.Certificates.Terminal030.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal030.polynomial_28, 233280000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal030.polynomial_29, 1133740800000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal030.polynomial_30, 30110940277862400000000000000000, by norm_num, R7.Core.Certificates.Terminal030.positive_30⟩
theorem bound_123 : minorBindings polynomial_123 witness_123 := by
 decide +kernel
theorem positive_123 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_123 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_123 ρ hρ u
def polynomial_124 : BiPoly := [[464415766896464640,15557934093650076100,60259524956850717600],[0,23393494399701620000,63248664179619000000],[5144162225315605920,355753541502913951300,993475123849225545300],[0,179289069226599800400,429204915412138260000],[22954690877666904720,2642510859533391185250,4805229735050909487300],[0,277684645425420195000,1031782820774443875000],[52659338933010513600,7205155990759309594500,9851274851624644824000],[0,-14876212271494833000,1006346095812536850000],[65002739117376443040,8122273946334743706000,8801248121184359433600],[0,-79766910571668364800,306074844022147200000],[40265612042490228240,3394999181598941901600,2675854808331061341600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_124 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal031.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_1, 1840000, by norm_num, R7.Core.Certificates.Terminal031.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_2, 16000, by norm_num, R7.Core.Certificates.Terminal031.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_3, 1440000000, by norm_num, R7.Core.Certificates.Terminal031.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_4, 544320000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_5, 22221319680000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_6, 4131221006122721280000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_6⟩
theorem bound_124 : minorBindings polynomial_124 witness_124 := by
 decide +kernel
theorem positive_124 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_124 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_124 ρ hρ u
def polynomial_125 : BiPoly := [[1651234026877395840,65900847359322685975,241494482840001525600],[0,71801977471976451000,180611593903501200000],[17864467666911286920,1357855637400311003800,3667355271603679335300],[0,495452078587033952100,1171377763173069615000],[77715202661777252880,9284823933771638475375,16874226112838531884200],[0,711440406831778668000,2674580459796004050000],[173597312245263472800,24096465244822645701000,33151291809420431727000],[0,-40253228454159756000,2461120815153949200000],[208260918335915595360,26182978312041627174000,28425692703585973622400],[0,-182719082800463227200,701114213490490800000],[125067431344098436200,10545073215572471058000,8311367207694963258000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_125 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal031.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal031.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal031.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal031.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal031.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal031.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal031.polynomial_11, 8640000000, by norm_num, R7.Core.Certificates.Terminal031.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal031.polynomial_12, 4354560000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal031.polynomial_13, 148142131200000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal031.polynomial_14, 82624420122454425600000000000000000, by norm_num, R7.Core.Certificates.Terminal031.positive_14⟩
theorem bound_125 : minorBindings polynomial_125 witness_125 := by
 decide +kernel
theorem positive_125 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_125 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_125 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry020
