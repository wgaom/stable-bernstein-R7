import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal040
import R7.Certificates.Spectral.Terminal.Terminal041

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry027
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_162 : BiPoly := [[1038689063622408960,60912663357482600400,202231560397373906400],[0,3441564676816944000,105375797939647800000],[10176768092049230160,976211558797976567400,2450593783998197001900],[0,69473100925693349400,601167691700462610000],[40048002964993524480,5284998991316474083500,9585116218622395078200],[0,104675088621353805000,1167244160510487375000],[79795719263222254800,11511037985371040083500,16086111860287996857000],[0,-58057765511856007500,888752281537167750000],[83654533517123675520,10682414643670642728000,11652739240661304076800],[0,-56221256246296377600,215727450304766400000],[42880262175119463840,3615453673910561505600,2849611614066844545600],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
def witness_162 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_16, 1656000, by norm_num, R7.Core.Certificates.Terminal040.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_17, 66240000, by norm_num, R7.Core.Certificates.Terminal040.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_18, 1296000, by norm_num, R7.Core.Certificates.Terminal040.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_19, 349920000000, by norm_num, R7.Core.Certificates.Terminal040.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_20, 1574640000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_21, 422431822080000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_22, 67316018085189181440000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_22⟩
theorem bound_162 : minorBindings polynomial_162 witness_162 := by
 decide +kernel
theorem positive_162 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_162 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_162 ρ hρ u
def polynomial_163 : BiPoly := [[28951623384664320,666749777373604300,2643020197727488800],[0,1416007997261406000,5683071447997200000],[344620112426966880,18382130429480910700,56464063813451756700],[0,16508435756814549600,44691597317064240000],[1690390686581805600,176243252879191948125,320741498275882816500],[0,33351408772348122000,126420858591586200000],[4282433202016337400,563526942880120398000,756673438867862953500],[0,-1673403928738605000,146775102258467250000],[5831565406029212760,715824626446777441500,771335408964958538400],[0,-13900860060897456000,53339204745684000000],[3965552701154340660,334355980005956399400,263531155365937859400],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
def witness_163 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal040.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal040.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal040.polynomial_25, 1840000, by norm_num, R7.Core.Certificates.Terminal040.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal040.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal040.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal040.polynomial_27, 4320000000, by norm_num, R7.Core.Certificates.Terminal040.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal040.polynomial_28, 77760000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal040.polynomial_29, 37791360000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal040.polynomial_30, 752773506946560000000000000000, by norm_num, R7.Core.Certificates.Terminal040.positive_30⟩
theorem bound_163 : minorBindings polynomial_163 witness_163 := by
 decide +kernel
theorem positive_163 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_163 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_163 ρ hρ u
def polynomial_164 : BiPoly := [[231216389496702720,6214186357821490300,23214858409390444800],[0,11221540896566982000,40340726825760900000],[2761150809597217920,159800936976753361300,474267794560450687800],[0,119268227471400836700,314284599676164105000],[13488503032808793360,1446508812993072904500,2632230040051257152400],[0,232245196951218921000,880631726098470975000],[34070660945901522000,4532470674215271412500,6118068956241416355000],[0,-12773218492911523500,1011577873255236450000],[46334190354817849920,5715518039268168888000,6168346817418691372800],[0,-95143664416809254400,365077223592681600000],[31550111600392776240,2660150873893543221600,2096665455878450661600],[0,0,0],[8080783902214943040,-34040762012541398400,40582148118788073600]]
def witness_164 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_0, 12098000, by norm_num, R7.Core.Certificates.Terminal041.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_1, 42320000, by norm_num, R7.Core.Certificates.Terminal041.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_2, 368000, by norm_num, R7.Core.Certificates.Terminal041.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_3, 496800000000, by norm_num, R7.Core.Certificates.Terminal041.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_4, 2235600000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_5, 4346006400000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_6, 692551626390835200000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_6⟩
theorem bound_164 : minorBindings polynomial_164 witness_164 := by
 decide +kernel
theorem positive_164 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_164 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_164 ρ hρ u
def polynomial_165 : BiPoly := [[895715635811840640,28790568170336486100,103929240111480057600],[0,40262210500332768000,134079813110001600000],[10526363722816707960,677874095247669903150,1932840664915735503900],[0,385979938813127257200,1015795446768103680000],[50566102604573928120,5644388593178284854000,10267130517370236280800],[0,709084157529792096000,2755411049330391600000],[125520777580542987600,16959319050013797897000,23056305237948471984000],[0,-47639133669784104000,3053294929750627800000],[167740491876639887520,20835372177629130618000,22535217541658500156800],[0,-276781569212536012800,1062042832269619200000],[112255645694215181760,9464846203245534998400,7459958859589625558400],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_165 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_8, 138000, by norm_num, R7.Core.Certificates.Terminal041.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_9, 24840000, by norm_num, R7.Core.Certificates.Terminal041.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_10, 54000, by norm_num, R7.Core.Certificates.Terminal041.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_11, 29160000000, by norm_num, R7.Core.Certificates.Terminal041.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_12, 44089920000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_13, 2399902525440000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_14, 1338515605983761694720000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_14⟩
theorem bound_165 : minorBindings polynomial_165 witness_165 := by
 decide +kernel
theorem positive_165 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_165 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_165 ρ hρ u
def polynomial_166 : BiPoly := [[2152632518165914560,82153670710148765025,289698189517039910400],[0,80987939826692478000,272071555832253600000],[24701091736159633680,1779135986177313962700,4880496977834641643700],[0,709112649358732206000,1970053680557516400000],[115457757124107399120,13481709638363628249000,24507942517146374920800],[0,1213320438455938281000,5066033068363664475000],[278306665948272155400,38278228556847029305500,52449984374785007886000],[0,-113906760479071560000,5284314181346854500000],[360344458165338964800,45115042365903969900000,48916377475514392032000],[0,-449770049970371020800,1725819602438131200000],[233052481821685866480,19649843748042360703200,15487523284582809583200],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
def witness_166 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_16, 34500, by norm_num, R7.Core.Certificates.Terminal041.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_17, 12420000, by norm_num, R7.Core.Certificates.Terminal041.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_18, 1296000, by norm_num, R7.Core.Certificates.Terminal041.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_19, 349920000000, by norm_num, R7.Core.Certificates.Terminal041.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_20, 1763596800000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_21, 23999025254400000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_22, 26770312119675233894400000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_22⟩
theorem bound_166 : minorBindings polynomial_166 witness_166 := by
 decide +kernel
theorem positive_166 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_166 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_166 ρ hρ u
def polynomial_167 : BiPoly := [[3509516778182960400,157127605790165405375,541793430310152936000],[0,93502963891332240000,369438635852838000000],[38881711810695269700,3114751408988724183000,8252734826826242523000],[0,774907369364056812000,2515167058200967800000],[175006351443342837600,21368047987813078798125,38815136608059134446500],[0,1231199279368126920000,6014766251351738250000],[404771466879961029000,56669880069845330917500,78239160121443207547500],[0,-185052710609887365000,5777670766876611750000],[500861204768869232400,63192581906900360985000,68680146681392717016000],[0,-454094761989316896000,1742414021692344000000],[308092940628144928200,25976887677385843338000,20474343609199787538000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
def witness_167 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal041.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal041.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal041.polynomial_25, 34500000, by norm_num, R7.Core.Certificates.Terminal041.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal041.polynomial_26, 54000000, by norm_num, R7.Core.Certificates.Terminal041.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal041.polynomial_27, 24300000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal041.polynomial_28, 15309000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal041.polynomial_29, 520812180000000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal041.polynomial_30, 726191192482509600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal041.positive_30⟩
theorem bound_167 : minorBindings polynomial_167 witness_167 := by
 decide +kernel
theorem positive_167 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_167 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_167 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry027
