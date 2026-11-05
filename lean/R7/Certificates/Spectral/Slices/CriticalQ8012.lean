import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal119
import R7.Certificates.Spectral.Terminal.Terminal120

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8012
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_72 : BiPoly := [[258823872135],[290269248750],[4528969720860],[1576744740000],[16430905197504],[2246359050000],[17582379519600],[0],[388946471760]]
def witness_72 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_17, 517647744270, by norm_num, R7.Core.Certificates.Terminal119.positive_17⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_18, 4604565682970731752381900, by norm_num, R7.Core.Certificates.Terminal119.positive_18⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_19, 150027427957449477465680188631869555200, by norm_num, R7.Core.Certificates.Terminal119.positive_19⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_20, 5252443121054511526505181120929416537349733363840000, by norm_num, R7.Core.Certificates.Terminal119.positive_20⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_21, 4085838440108469657728883840690516908395150106084648730316800000, by norm_num, R7.Core.Certificates.Terminal119.positive_21⟩
theorem bound_72 : ordinaryBindings polynomial_72 witness_72 := by
 decide +kernel
theorem positive_72 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_72 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_72 ρ hρ u
def polynomial_73 : BiPoly := [[762242858340],[468115571250],[11368143011250],[2376308182500],[37940428672992],[2945556900000],[37174173841440],[0],[777892943520]]
def witness_73 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_22, 1524485716680, by norm_num, R7.Core.Certificates.Terminal119.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_23, 34442011103605665278737500, by norm_num, R7.Core.Certificates.Terminal119.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_24, 2604880803455638425660901587062965200000, by norm_num, R7.Core.Certificates.Terminal119.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_25, 193369754239093251916796424861877403744707075776000000, by norm_num, R7.Core.Certificates.Terminal119.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_26, 300841934625574495178651306128836646064691315591128656343040000000, by norm_num, R7.Core.Certificates.Terminal119.positive_26⟩
theorem bound_73 : ordinaryBindings polynomial_73 witness_73 := by
 decide +kernel
theorem positive_73 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_73 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_73 ρ hρ u
def polynomial_74 : BiPoly := [[1270701840930],[398649288750],[15860577720990],[1760664172500],[47431774572480],[1844692200000],[41193003445920],[0],[777892943520]]
def witness_74 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_27, 2541403681860, by norm_num, R7.Core.Certificates.Terminal119.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_28, 80457339977680466731920300, by norm_num, R7.Core.Certificates.Terminal119.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_29, 7624590630364301497869329343457241688000, by norm_num, R7.Core.Certificates.Terminal119.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_30, 627885788798310427978827914410747546684872555025920000, by norm_num, R7.Core.Certificates.Terminal119.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_31, 976855848885389484846322821161038070828628259370352157392076800000, by norm_num, R7.Core.Certificates.Terminal119.positive_31⟩
theorem bound_74 : ordinaryBindings polynomial_74 witness_74 := by
 decide +kernel
theorem positive_74 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_74 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_74 ρ hρ u
def polynomial_75 : BiPoly := [[157577731020],[105091117500],[2405565268725],[552623287500],[8516738868984],[714074400000],[8791189759800],[0],[194473235880]]
def witness_75 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_0, 315155462040, by norm_num, R7.Core.Certificates.Terminal120.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_1, 1505209924487409467148000, by norm_num, R7.Core.Certificates.Terminal120.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_2, 25542713625949559334115205004525264000, by norm_num, R7.Core.Certificates.Terminal120.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_3, 448334175006588475633725885284054473794383174400000, by norm_num, R7.Core.Certificates.Terminal120.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_4, 174377995538242962352014413144215492969968715388388754944000000, by norm_num, R7.Core.Certificates.Terminal120.positive_4⟩
theorem bound_75 : ordinaryBindings polynomial_75 witness_75 := by
 decide +kernel
theorem positive_75 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_75 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_75 ρ hρ u
def polynomial_76 : BiPoly := [[751955259060],[212579463750],[11191111030230],[1107385447500],[37453791311136],[1249630200000],[36671820140880],[0],[777892943520]]
def witness_76 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_5, 1503910518120, by norm_num, R7.Core.Certificates.Terminal120.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_6, 33615669147215055001472700, by norm_num, R7.Core.Certificates.Terminal120.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_7, 2516224264775707747378572408619569974400, by norm_num, R7.Core.Certificates.Terminal120.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_8, 184496553933992130357180202030710754280544851986944000, by norm_num, R7.Core.Certificates.Terminal120.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_9, 287037134818019148136124912649475740170024949563013177538805760000, by norm_num, R7.Core.Certificates.Terminal120.positive_9⟩
theorem bound_76 : ordinaryBindings polynomial_76 witness_76 := by
 decide +kernel
theorem positive_76 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_76 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_76 ρ hρ u
def polynomial_77 : BiPoly := [[1773467605080],[0],[22458732815700],[0],[68121715357872],[0],[60282444067200],[0],[1166839415280]]
def witness_77 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_10, 3546935210160, by norm_num, R7.Core.Certificates.Terminal120.positive_10⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_11, 159319340399164336095024000, by norm_num, R7.Core.Certificates.Terminal120.positive_11⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_12, 21706213515351580257918354266316857856000, by norm_num, R7.Core.Certificates.Terminal120.positive_12⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_13, 2617007204299764650882189881927040953313545823846400000, by norm_num, R7.Core.Certificates.Terminal120.positive_13⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_14, 6107254312097369774153975555987361411169983175200838513065984000000, by norm_num, R7.Core.Certificates.Terminal120.positive_14⟩
theorem bound_77 : ordinaryBindings polynomial_77 witness_77 := by
 decide +kernel
theorem positive_77 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_77 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_77 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8012
