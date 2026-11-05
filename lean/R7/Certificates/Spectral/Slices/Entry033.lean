import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal049
import R7.Certificates.Spectral.Terminal.Terminal050

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry033
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_198 : BiPoly := [[1629024562363132800,73032777293242959500,235382147932413702000],[0,30446607709491800000,134834746587660000000],[19089623590915515300,1475979747968868942000,3930837202642224064500],[0,297004792932682614000,986130407746641600000],[90680295566331198000,10891376310118247795625,19793230228744316257500],[0,530775383465447820000,2589751272029331375000],[222188768737881714000,30926912512272367680000,42600252145603224510000],[0,-86938862885435925000,2774823639671553750000],[292614946500413577600,36836215876947773790000,40007537988967128384000],[0,-244466359959857112000,938045643953418000000],[192176784748248816600,16203405184904040894000,12771125221580065494000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
def witness_198 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_16, 230000, by norm_num, R7.Core.Certificates.Terminal049.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_17, 46000000, by norm_num, R7.Core.Certificates.Terminal049.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_18, 6000000, by norm_num, R7.Core.Certificates.Terminal049.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_19, 97200000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_20, 15309000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_21, 4687309620000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_22, 4357147154895057600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_22⟩
theorem bound_198 : minorBindings polynomial_198 witness_198 := by
 decide +kernel
theorem positive_198 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_198 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_198 ρ hρ u
def polynomial_199 : BiPoly := [[1826629306902982080,91815624814539447950,298221936553798687200],[0,9055854326898019000,116484865212750300000],[20498611824132305040,1733830693738572488100,4497840547795279916100],[0,140768911911928644900,791974811423170935000],[92806521923911204080,11593615629244635939750,21053610758685508117200],[0,259620799603569264000,1917701668816608150000],[215769409950089689200,30503097437940697329000,42287007604020351228000],[0,-95323999163465331000,1886055958164476700000],[268161953977232723520,33980263056218045448000,36980064606375172396800],[0,-154728585566730201600,593711444428502400000],[165129681709606390560,13922925936658286990400,10973707597802130350400],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
def witness_199 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal049.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_25, 920000, by norm_num, R7.Core.Certificates.Terminal049.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal049.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_27, 8640000000, by norm_num, R7.Core.Certificates.Terminal049.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_28, 544320000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_29, 34566497280000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_30, 25705375149208043520000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_30⟩
theorem bound_199 : minorBindings polynomial_199 witness_199 := by
 decide +kernel
theorem positive_199 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_199 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_199 ρ hρ u
def polynomial_200 : BiPoly := [[54333868543822080,1835921338332066700,5502107234241787200],[0,2241409611817611000,7230785171330700000],[689240224853933760,42048886273600638900,120538442227528575900],[0,23573284799400886500,59496994885749975000],[3529454288971408560,383876689861632870750,698814389294298770400],[0,47620542246220512000,178376130498298950000],[9388741328669084400,1256862739890424383000,1702285287607808496000],[0,-2959674489847971000,221812389277274700000],[13529147970173716800,1673981233721365500000,1808349132112127712000],[0,-22893515211403958400,87845060655237600000],[9819463831429795920,827929093348082512800,652553337096608032800],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_200 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal050.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_1, 5520000, by norm_num, R7.Core.Certificates.Terminal050.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_2, 144000, by norm_num, R7.Core.Certificates.Terminal050.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_3, 25920000000, by norm_num, R7.Core.Certificates.Terminal050.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_4, 1166400000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_5, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_6, 40147920370483200000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_6⟩
theorem bound_200 : minorBindings polynomial_200 witness_200 := by
 decide +kernel
theorem positive_200 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_200 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_200 ρ hρ u
def polynomial_201 : BiPoly := [[401753349159793920,15005654415651683300,44738488759538902800],[0,14257288838990832000,42323334393105900000],[5012703793371580560,324886009657601310900,910770356685561912900],[0,139885933499008102800,344225393421767820000],[25463800908834114960,2834749058751277107000,5159103624084924221400],[0,272141320442994369000,1016304940632019275000],[67162970418797307600,9073562427455298034500,12340939583848710159000],[0,-17588278170644422500,1240794846013920750000],[95994121727690786880,11928128290423894332000,12902809029272661139200],[0,-125176386770600054400,480316246191381600000],[69142970173973119200,5829796574462829528000,4594902196124044728000],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_201 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_8, 46000, by norm_num, R7.Core.Certificates.Terminal050.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_9, 5520000, by norm_num, R7.Core.Certificates.Terminal050.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_10, 144000, by norm_num, R7.Core.Certificates.Terminal050.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal050.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_12, 408240000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_13, 18517766400000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_14, 6885368343537868800000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_14⟩
theorem bound_201 : minorBindings polynomial_201 witness_201 := by
 decide +kernel
theorem positive_201 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_201 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_201 ρ hρ u
def polynomial_202 : BiPoly := [[1396717529519747520,57708966259039050425,175640961504209476800],[0,37666818618422694000,109797446962747800000],[17071265295679309200,1202565086344214770500,3282275919805429765500],[0,344321015242025074200,862956253763887230000],[84802623853710606480,9766677498329735271000,17765159326992428083200],[0,634365526407775749000,2451208879574054775000],[218472749546552908200,29909288436147229216500,40916607874745403438000],[0,-49676092562707884000,2863844359016923800000],[304518921277885312320,38062046181913357968000,41247701967425308588800],[0,-274619213203063075200,1053745622642512800000],[213529760831387574000,18003783538782267660000,14190139135088961660000],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
def witness_202 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_16, 11500, by norm_num, R7.Core.Certificates.Terminal050.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_17, 20700000, by norm_num, R7.Core.Certificates.Terminal050.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_18, 18000000, by norm_num, R7.Core.Certificates.Terminal050.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_19, 4860000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_20, 88179840000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_21, 29998781568000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_22, 33462890149594042368000000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_22⟩
theorem bound_202 : minorBindings polynomial_202 witness_202 := by
 decide +kernel
theorem positive_202 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_202 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_202 ρ hρ u
def polynomial_203 : BiPoly := [[2956139216485502400,134688472768798151000,421554290566224216000],[0,45431459105326280000,160478687545461000000],[34943850913567219200,2686753778916686238000,7146845613902499228000],[0,406872429988126983000,1190605276439586450000],[167817099487157568000,20069980710227516452500,36480791040126975495000],[0,714739467482323560000,3179268661350219750000],[416743399378583856000,57907565211668549445000,79718321489687258040000],[0,-92355157814687460000,3467074421602984500000],[557962167525337713600,70190194952162147940000,76216456468552254624000],[0,-311139003585272688000,1193876274122532000000],[374185485647383939200,31549487344151783328000,24866529531965418528000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
def witness_203 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal050.polynomial_24, 460000, by norm_num, R7.Core.Certificates.Terminal050.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal050.polynomial_25, 368000000, by norm_num, R7.Core.Certificates.Terminal050.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal050.polynomial_26, 2304000000, by norm_num, R7.Core.Certificates.Terminal050.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal050.polynomial_27, 2073600000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal050.polynomial_28, 114960384000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal050.polynomial_29, 1896219279360000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal050.polynomial_30, 3525308591891388825600000000000000000000000, by norm_num, R7.Core.Certificates.Terminal050.positive_30⟩
theorem bound_203 : minorBindings polynomial_203 witness_203 := by
 decide +kernel
theorem positive_203 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_203 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_203 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry033
