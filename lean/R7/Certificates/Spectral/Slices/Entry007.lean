import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal010
import R7.Certificates.Spectral.Terminal.Terminal011

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry007
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_42 : BiPoly := [[1636559916394757760,84767642942896747400,301493745839527298400],[0,29563811920261125000,201068508437212500000],[13716718456629578400,1248490006200168351000,3193372712255033556000],[0,189185545763372586900,922188052629435735000],[46570602851209584000,6016455635775512145000,10915591194785550060000],[0,208174748231261214000,1487382039929084400000],[81414862344278532000,11648520307733070060000,16224150851683704630000],[0,-49933458897783552000,974190795992051400000],[76408271601210198720,9724971004133827428000,10597738388187177964800],[0,-54058900236823440000,207430240677660000000],[35791655148880202880,3017777050310170579200,2378537607405387859200],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
def witness_42 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_16, 644000, by norm_num, R7.Core.Certificates.Terminal010.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_17, 55200000, by norm_num, R7.Core.Certificates.Terminal010.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_18, 144000000, by norm_num, R7.Core.Certificates.Terminal010.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_19, 259200000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_20, 261273600000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_21, 9481096396800000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_22, 1175102863963796275200000000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_22⟩
theorem bound_42 : minorBindings polynomial_42 witness_42 := by
 decide +kernel
theorem positive_42 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_42 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_42 ρ hρ u
def polynomial_43 : BiPoly := [[1099368493456020480,66124616489149655200,222562792274697643200],[0,7995613580852466000,121054031265994200000],[8614979071901486640,845342274228196734600,2110404368570563947600],[0,66150312110600173500,505628226921764025000],[27259416718476233760,3626304594324317187000,6575589266864785538400],[0,69644155910749866000,739493152033008600000],[44231785016417240400,6394734652789359918000,8944096068951880536000],[0,-28401937729236139500,438569402200050150000],[38409376745044267200,4907541121432609860000,5354230780482082848000],[0,-22344345431220355200,85737832813432800000],[16617554176265808480,1401110773358293483200,1104321032009644363200],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_43 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_24, 368000, by norm_num, R7.Core.Certificates.Terminal010.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_25, 44160000, by norm_num, R7.Core.Certificates.Terminal010.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_26, 1152000, by norm_num, R7.Core.Certificates.Terminal010.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_27, 414720000000, by norm_num, R7.Core.Certificates.Terminal010.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_28, 2332800000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_29, 3023308800000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_30, 160591681481932800000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_30⟩
theorem bound_43 : minorBindings polynomial_43 witness_43 := by
 decide +kernel
theorem positive_43 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_43 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_43 ρ hρ u
def polynomial_44 : BiPoly := [[473834959435995840,31428967450527224100,102316291526124525600],[0,199965781339449000,47440038435666300000],[3403254544909469280,349041897749040004200,859517578239597160200],[0,14463711253102248900,180160343767756035000],[9810375828029587440,1325968527736014280500,2403684844776076494600],[0,15546955138871508000,238630652037502425000],[14486467424856868800,2105463028335113736000,2951050695936337242000],[0,-9350625373079737500,128177059656060000000],[11464172753673517920,1467508631262962418000,1601985218272006492800],[0,-5972221359496684800,22916102779627200000],[4532060229890675040,382121120006807313600,301178463275357553600],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_44 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_0, 1242000, by norm_num, R7.Core.Certificates.Terminal011.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_1, 33120000, by norm_num, R7.Core.Certificates.Terminal011.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_2, 10368000, by norm_num, R7.Core.Certificates.Terminal011.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_3, 3732480000000, by norm_num, R7.Core.Certificates.Terminal011.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_4, 4199040000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_5, 16325867520000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_6, 216798770000609280000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_6⟩
theorem bound_44 : minorBindings polynomial_44 witness_44 := by
 decide +kernel
theorem positive_44 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_44 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_44 ρ hρ u
def polynomial_45 : BiPoly := [[105296657652443520,6984214989006049800,22736953672472116800],[0,44143966891038000,9830970566175600000],[652840380152301240,66983549404668738600,164936663002841511600],[0,2651523079756605600,32810992182170640000],[1651694996166077520,223329786079240059000,404841501233419726800],[0,2532948111199638000,38630651516659800000],[2168393030813883600,315218318018326767000,441847697574521124000],[0,-1355087552953752000,18612963871578900000],[1541401378645178880,197330741421964632000,215419472316794419200],[0,-783711040470350400,3007189732575600000],[551981694666171960,46540392821341916400,36681992321998676400],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
def witness_45 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_8, 276000, by norm_num, R7.Core.Certificates.Terminal011.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_9, 198720000, by norm_num, R7.Core.Certificates.Terminal011.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_10, 3456000, by norm_num, R7.Core.Certificates.Terminal011.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_11, 622080000000, by norm_num, R7.Core.Certificates.Terminal011.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_12, 89579520000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_13, 29023764480000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_14, 42824448395182080000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_14⟩
theorem bound_45 : minorBindings polynomial_45 witness_45 := by
 decide +kernel
theorem positive_45 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_45 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_45 ρ hρ u
def polynomial_46 : BiPoly := [[14674110482638080,272774390703429200,1384821074676727200],[0,698009415973852000,2848033355342400000],[142456946170417920,7768052926195393800,23862859612713937800],[0,6356689621785176400,17239328968677660000],[568894536287370720,60412417457019871500,109914742310611114800],[0,9895579015980204000,37854596211244650000],[1184320204164838800,157284634742629236000,212102350482668292000],[0,-453200937237468000,34546053754362600000],[1341396172584561240,165465301804348738500,178574239087482621600],[0,-2625718011502852800,10075183118629200000],[769869205718608260,64911600513976883400,51161726133313943400],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
def witness_46 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_16, 184000, by norm_num, R7.Core.Certificates.Terminal011.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_17, 14720000, by norm_num, R7.Core.Certificates.Terminal011.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_18, 1152000, by norm_num, R7.Core.Certificates.Terminal011.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_19, 414720000000, by norm_num, R7.Core.Certificates.Terminal011.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_20, 515082240000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_21, 3627970560000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_22, 12044376111144960000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_22⟩
theorem bound_46 : minorBindings polynomial_46 witness_46 := by
 decide +kernel
theorem positive_46 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_46 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_46 ρ hρ u
def polynomial_47 : BiPoly := [[119772469344775680,2802363472808723200,12679954682945611200],[0,5811577866525547000,20663564735651400000],[1163747552906869920,69499790283145346300,205545810278083492800],[0,47179250024168864100,123362721415614915000],[4631263158177139680,507199854154128621000,922661597543015446200],[0,70147949321549142000,267013784616337575000],[9603292090293149400,1290319375101236163000,1749611799003353346000],[0,-3370605772848426000,239339622487036950000],[10831695557544653760,1343083274774478774000,1451864192309545478400],[0,-17796533189074891200,68287352248486800000],[6188005313889190920,521742298470833062800,411224440241353582800],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_47 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_24, 736000, by norm_num, R7.Core.Certificates.Terminal011.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_25, 11040000, by norm_num, R7.Core.Certificates.Terminal011.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal011.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_27, 25920000000, by norm_num, R7.Core.Certificates.Terminal011.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_28, 2799360000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_29, 2720977920000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_30, 72266256666869760000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_30⟩
theorem bound_47 : minorBindings polynomial_47 witness_47 := by
 decide +kernel
theorem positive_47 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_47 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_47 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry007
