import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal012
import R7.Certificates.Spectral.Terminal.Terminal013

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry008
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_48 : BiPoly := [[470563029395948160,13950068950801729650,57815272108504184400],[0,21629634581764659000,70367146801143300000],[4496297363503815600,299860270236319327750,850385239438496904000],[0,156049263327568192800,405754385609438820000],[17591943396280168440,2005433156347393285500,3646575669788434097100],[0,217182270442651398000,844469847653427675000],[35821395160753892400,4886645126756589783000,6671588356392834028500],[0,-12103940986708032000,725006290672506150000],[39626162344219333680,4945904001120579147000,5357500792483285051200],[0,-51416020669689849600,197289206688974400000],[22166422791067852920,1868964195930730642800,1473071586404473162800],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_48 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal012.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_1, 158700000, by norm_num, R7.Core.Certificates.Terminal012.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_2, 5750000, by norm_num, R7.Core.Certificates.Terminal012.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_3, 517500000000, by norm_num, R7.Core.Certificates.Terminal012.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_4, 391230000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_5, 887309640000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_6, 82480974948630720000000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_6⟩
theorem bound_48 : minorBindings polynomial_48 witness_48 := by
 decide +kernel
theorem positive_48 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_48 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_48 ρ hρ u
def polynomial_49 : BiPoly := [[1143589123694240640,42118453705510960475,162874461178452057600],[0,45322859137539224000,146757317791708800000],[10650489811943138280,795065742180695351700,2166358013438647682700],[0,293295460229845752300,800816464007498745000],[40502168173557069840,4822557137692682678625,8763537073932966473100],[0,376704923641376796000,1566982893711486600000],[79984523933451432000,11094655511111601555000,15257188293850082880000],[0,-27771455337152782500,1257170300976429000000],[85585473831132989280,10757986659373548042000,11678800349957397955200],[0,-83250706364708097600,319442570643596400000],[46163100674976170760,3892246536479595008400,3067772936823994568400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_49 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal012.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal012.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal012.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_11, 129600000000, by norm_num, R7.Core.Certificates.Terminal012.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_12, 6123600000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_13, 13888324800000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_14, 2582013128826700800000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_14⟩
theorem bound_49 : minorBindings polynomial_49 witness_49 := by
 decide +kernel
theorem positive_49 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_49 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_49 ρ hρ u
def polynomial_50 : BiPoly := [[1880492215819827600,84094828496922445875,306411282377739234000],[0,56047734403427245000,205355684597206500000],[16867661847797875500,1399186109398356120000,3679164540666022545000],[0,332141028127112460000,1041369565133799000000],[61640707370791052700,7655886197768288878125,13902088254651105993000],[0,390460498479153450000,1876347890545010625000],[116586883866516921000,16434551097575699107500,22753985458676985765000],[0,-43605812001912300000,1377605302555860000000],[119039747774717347200,15062140973979061830000,16384516931679882048000],[0,-84091622590614240000,322669263276360000000],[61008503094682164000,5143938153937790760000,4054325467168274760000],[0,0,0],[11784476524063458600,-49642777934956206000,59182299339899274000]]
def witness_50 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_16, 517500, by norm_num, R7.Core.Certificates.Terminal012.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_17, 57500000, by norm_num, R7.Core.Certificates.Terminal012.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_18, 750000000, by norm_num, R7.Core.Certificates.Terminal012.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_19, 337500000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_20, 136930500000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_21, 4050761400000000000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_22, 941358953218068000000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_22⟩
theorem bound_50 : minorBindings polynomial_50 witness_50 := by
 decide +kernel
theorem positive_50 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_50 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_50 ρ hρ u
def polynomial_51 : BiPoly := [[2140734590747559360,113381107329993229525,391669422862708442400],[0,38647490736522329000,198960935517672300000],[18296290284990366240,1662547424103845381100,4244136037402529924100],[0,222150346207612431300,923817177673082595000],[63414090130238169840,8171813987768247567375,14828565041506329848100],[0,239945852947951827000,1509628523288591700000],[113308548228901207800,16192928490280913128500,22545520603211844252000],[0,-46243975744842687000,1003084343923602150000],[108836340822598717440,13844919608529122106000,15084990734876184729600],[0,-56341387135711540800,216188406395161200000],[52263950984444387160,4406640351873374084400,3473205483540822044400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_51 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_24, 11500, by norm_num, R7.Core.Certificates.Terminal012.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_25, 460000, by norm_num, R7.Core.Certificates.Terminal012.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal012.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_27, 4320000000, by norm_num, R7.Core.Certificates.Terminal012.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_28, 544320000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_29, 28393908480000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_30, 5278782396712366080000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_30⟩
theorem bound_51 : minorBindings polynomial_51 witness_51 := by
 decide +kernel
theorem positive_51 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_51 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_51 ρ hρ u
def polynomial_52 : BiPoly := [[1664073873549704160,100691011371652527775,333390742148390474400],[0,11431796433187654000,132615533142649800000],[13311606515957452440,1298285116795170887850,3241599550300538994600],[0,81149062532729551200,558824149649199780000],[43056762612756802560,5704813654642539553875,10346345204058360792900],[0,84169107142300818000,827526509860481550000],[71505477834068383200,10319740303055400391500,14425038982632041500500],[0,-31345588781129448000,499072433217967350000],[63639352843601970960,8124939878382078129000,8862431570924907326400],[0,-25948272113675251200,99566515525276800000],[28267273100536069320,2383358011324509718800,1878504133121300638800],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_52 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_0, 11500, by norm_num, R7.Core.Certificates.Terminal013.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_1, 230000, by norm_num, R7.Core.Certificates.Terminal013.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_2, 6000, by norm_num, R7.Core.Certificates.Terminal013.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_3, 540000000, by norm_num, R7.Core.Certificates.Terminal013.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_4, 408240000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_5, 925888320000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_6, 86067104294223360000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_6⟩
theorem bound_52 : minorBindings polynomial_52 witness_52 := by
 decide +kernel
theorem positive_52 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_52 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_52 ρ hρ u
def polynomial_53 : BiPoly := [[814710579971872320,53911979081418386800,173857943880703708800],[0,-246115982977242000,57091539737627100000],[5982406130998524600,608642141887168731500,1500426801021137589000],[0,16297380029974187100,220581547566547365000],[17645234829572004480,2373872353463652711000,4304037483529877653200],[0,18373714225150149000,298458435902163525000],[26690114746033686000,3871534182784769497500,5422582870280955990000],[0,-12180234657825076500,164490356667102300000],[21667579705792147680,2771315027962210422000,3024506235586551811200],[0,-7911477145770033600,30357251096000400000],[8802655446518426520,742196790782452666800,584981245977136786800],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_53 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_8, 184000, by norm_num, R7.Core.Certificates.Terminal013.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_9, 36800000, by norm_num, R7.Core.Certificates.Terminal013.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal013.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_11, 900000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_12, 4050000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_13, 3936600000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_14, 104551875964800000000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_14⟩
theorem bound_53 : minorBindings polynomial_53 witness_53 := by
 decide +kernel
theorem positive_53 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_53 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_53 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry008
