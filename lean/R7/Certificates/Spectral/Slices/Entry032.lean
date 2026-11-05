import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal048
import R7.Certificates.Spectral.Terminal.Terminal049

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry032
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_192 : BiPoly := [[390549467507509440,17383119188485668100,58228257923098749600],[0,9361998940438356000,40856053588837200000],[4516985045024887320,355860355549897384800,945843451431122683800],[0,86970583699249005600,291974904534230640000],[20960844513614389440,2543058516317366016750,4620135700094627424600],[0,149853927313857168000,746010029023654050000],[49981745427942182400,6983560569940391358000,9633381094371977316000],[0,-25182574801813170000,768150367888081500000],[63741973315821554880,8036646248495832912000,8732689506243090259200],[0,-64149894947697148800,246150552270823200000],[40265612042490228240,3394999181598941901600,2675854808331061341600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_192 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal048.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_1, 11040000, by norm_num, R7.Core.Certificates.Terminal048.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_2, 10368000, by norm_num, R7.Core.Certificates.Terminal048.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_3, 11197440000000, by norm_num, R7.Core.Certificates.Terminal048.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_4, 1410877440000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_5, 57597660610560000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_6, 10708124847870093557760000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_6⟩
theorem bound_192 : minorBindings polynomial_192 witness_192 := by
 decide +kernel
theorem positive_192 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_192 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_192 ρ hρ u
def polynomial_193 : BiPoly := [[368538301783552320,18796060964752976800,62218936590538408800],[0,3750723695512749000,31697989663101300000],[4072592696401359360,352632240239900352900,910442057845532004900],[0,42552765427897107900,211171410623819385000],[17992138299790198320,2273798951582264090250,4127824040009505598800],[0,71955169189244478000,498747321848661300000],[40655938989349490400,5773264022150043588000,8017401680723101536000],[0,-23076801719853903000,470405747572217100000],[48847344776521945920,6200834623014119508000,6751943473779556012800],[0,-36279528603379286400,139208739299229600000],[28877358131482890960,2434797392863887626400,1919047387792983386400],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
def witness_193 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_8, 2576000, by norm_num, R7.Core.Certificates.Terminal048.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_9, 11040000, by norm_num, R7.Core.Certificates.Terminal048.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_10, 144000, by norm_num, R7.Core.Certificates.Terminal048.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_11, 103680000000, by norm_num, R7.Core.Certificates.Terminal048.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_12, 11430720000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_13, 7407106560000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_14, 918049112471715840000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_14⟩
theorem bound_193 : minorBindings polynomial_193 witness_193 := by
 decide +kernel
theorem positive_193 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_193 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_193 ρ hρ u
def polynomial_194 : BiPoly := [[14277512902026240,393975386670175100,1258199123050761600],[0,675547549031087000,2510748331799400000],[179118660258393120,9632964083277134300,29148356612712768300],[0,8098315803140867700,21026539067829255000],[920550108837320640,96022938189378098625,174823453803975920100],[0,17113573654358841000,63797376917906100000],[2445878682514341000,322056826644390142500,432689735793212190000],[0,-875159443407532500,80088507969691500000],[3505850418277213920,430417655048057283000,463821253762927132800],[0,-8211804369307941600,31509641321987400000],[2512969294138098660,211881262055056619400,166999596623836079400],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_194 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal048.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal048.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal048.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_19, 7200000000, by norm_num, R7.Core.Certificates.Terminal048.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_20, 291600000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_21, 47239200000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_22, 627311255788800000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_22⟩
theorem bound_194 : minorBindings polynomial_194 witness_194 := by
 decide +kernel
theorem positive_194 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_194 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_194 ρ hρ u
def polynomial_195 : BiPoly := [[111443920151927040,3411822885012767100,10534903726444833600],[0,4943599807941959000,17273778498528300000],[1405714865887506240,80580742606709176100,237131868678379649100],[0,55966548011964357300,143603151157066995000],[7211654724320691120,767968442619145265250,1398108204510202450800],[0,116074836863655876000,433565638169923350000],[19172256058726448400,2545090046467984953000,3433044230780657256000],[0,-6460312263478101000,542166421156040700000],[27552549643282572480,3395651853913594632000,3663634147163836243200],[0,-55740732688635724800,213883625943187200000],[19871341007982190560,1675454141568308990400,1320551723591952350400],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
def witness_195 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal048.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal048.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal048.polynomial_25, 1840000, by norm_num, R7.Core.Certificates.Terminal048.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal048.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal048.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal048.polynomial_27, 66240000000, by norm_num, R7.Core.Certificates.Terminal048.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal048.polynomial_28, 25920000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal048.polynomial_29, 302330880000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal048.polynomial_30, 32118336296386560000000000000000, by norm_num, R7.Core.Certificates.Terminal048.positive_30⟩
theorem bound_195 : minorBindings polynomial_195 witness_195 := by
 decide +kernel
theorem positive_195 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_195 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_195 ρ hρ u
def polynomial_196 : BiPoly := [[425152606415892480,14840499219534756450,46113968002975873200],[0,16596954717684228000,55060833492341100000],[5277977481736715400,332657101943130583500,945423331199222323500],[0,173159433190206400800,446387876856821520000],[26673550388146877040,2942220759298672041750,5354306012136865683600],[0,343613790125806095000,1312607185260940125000],[69857727984795564000,9400066595221978597500,12759336845540241885000],[0,-23146593368613025500,1595454408649202850000],[98926135219678898880,12266829418555780992000,13260503780166235219200],[0,-159533821143336729600,612149688044294400000],[70363140235866762480,5932675337541585343200,4675988705467410223200],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_196 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_0, 207000, by norm_num, R7.Core.Certificates.Terminal049.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_1, 124200000, by norm_num, R7.Core.Certificates.Terminal049.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_2, 54000000, by norm_num, R7.Core.Certificates.Terminal049.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_3, 24300000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_4, 765450000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_5, 79857867600000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_6, 29693150981507059200000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_6⟩
theorem bound_196 : minorBindings polynomial_196 witness_196 := by
 decide +kernel
theorem positive_196 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_196 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_196 ρ hρ u
def polynomial_197 : BiPoly := [[1009043394471673920,40035217004637804550,126823728338587852800],[0,30784282265385250000,106027254145575000000],[12239775117656863200,855660952142279898000,2350286621059458438000],[0,300409751418232516200,823683484580802030000],[60283812437134272000,6935252090939394750000,12613064358186946980000],[0,563548605637238298000,2310838332171727050000],[153635509383760465200,21019749959556410409000,28742021648387185068000],[0,-53845496311545666000,2665765090661236200000],[211280892232663350720,26395676261840406528000,28600695801280769644800],[0,-252274867771842720000,968007789829080000000],[145606960719308098080,12276865727398193947200,9676323448308282427200],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
def witness_197 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal049.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal049.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal049.polynomial_9, 901600000, by norm_num, R7.Core.Certificates.Terminal049.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal049.polynomial_10, 288000000, by norm_num, R7.Core.Certificates.Terminal049.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal049.polynomial_11, 51840000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal049.polynomial_12, 901393920000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal049.polynomial_13, 355541114880000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal049.polynomial_14, 264398144391854161920000000000000000000, by norm_num, R7.Core.Certificates.Terminal049.positive_14⟩
theorem bound_197 : minorBindings polynomial_197 witness_197 := by
 decide +kernel
theorem positive_197 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_197 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_197 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry032
