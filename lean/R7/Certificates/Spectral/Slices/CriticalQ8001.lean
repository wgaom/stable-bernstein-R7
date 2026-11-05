import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal109
import R7.Certificates.Spectral.Terminal.Terminal110

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8001
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_6 : BiPoly := [[152834384538],[121074907500],[1125406928547],[259544299500],[2052227674872],[130913640000],[1088433017880],[0],[12964882392]]
def witness_6 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_7, 305668769076, by norm_num, R7.Core.Certificates.Terminal109.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_8, 673344367890993194175144, by norm_num, R7.Core.Certificates.Terminal109.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_9, 2743121053318233684797780004642563136, by norm_num, R7.Core.Certificates.Terminal109.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_10, 5959867020532584026671255683294385850487433743360, by norm_num, R7.Core.Certificates.Terminal109.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_11, 154537949986328802219301242361746623330876948713109421834240, by norm_num, R7.Core.Certificates.Terminal109.positive_11⟩
theorem bound_6 : ordinaryBindings polynomial_6 witness_6 := by
 decide +kernel
theorem positive_6 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_6 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_6 ρ hρ u
def polynomial_7 : BiPoly := [[81813013056],[49874980500],[493215627780],[91590394500],[766965627504],[38679030000],[351647590392],[0],[3704252112]]
def witness_7 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_12, 163626026112, by norm_num, R7.Core.Certificates.Terminal109.positive_12⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_13, 158918312700078124932720, by norm_num, R7.Core.Certificates.Terminal109.positive_13⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_14, 242397140776267489740259168075061760, by norm_num, R7.Core.Certificates.Terminal109.positive_14⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_15, 170238988442956221050876026218649429533165219840, by norm_num, R7.Core.Certificates.Terminal109.positive_15⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_16, 1261216264969128346702492759141199046271644879274528604160, by norm_num, R7.Core.Certificates.Terminal109.positive_16⟩
theorem bound_7 : ordinaryBindings polynomial_7 witness_7 := by
 decide +kernel
theorem positive_7 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_7 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_7 ρ hρ u
def polynomial_8 : BiPoly := [[20453253264],[11083329000],[98643125556],[16652799000],[127827604584],[5950620000],[50235370056],[0],[463031514]]
def witness_8 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_17, 40906506528, by norm_num, R7.Core.Certificates.Terminal109.positive_17⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_18, 7947451137275434259136, by norm_num, R7.Core.Certificates.Terminal109.positive_18⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_19, 2020463265765692168160377466958848, by norm_num, R7.Core.Certificates.Terminal109.positive_19⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_20, 202716021402350759916353382544023406006910976, by norm_num, R7.Core.Certificates.Terminal109.positive_20⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_21, 187727812603973751046239240156760658669633367360995328, by norm_num, R7.Core.Certificates.Terminal109.positive_21⟩
theorem bound_8 : ordinaryBindings polynomial_8 witness_8 := by
 decide +kernel
theorem positive_8 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_8 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_8 ρ hρ u
def polynomial_9 : BiPoly := [[1970514616],[21726441000],[81692547120],[80746776000],[269627212224],[77358060000],[234431726928],[0],[3704252112]]
def witness_9 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_22, 3941029232, by norm_num, R7.Core.Certificates.Terminal109.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_23, 171867193946433823680, by norm_num, R7.Core.Certificates.Terminal109.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_24, 66984469289866610704125481328640, by norm_num, R7.Core.Certificates.Terminal109.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_25, 30378070028289011396472894369986542211235840, by norm_num, R7.Core.Certificates.Terminal109.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_26, 225056060121546940423553576641551116795095020900188160, by norm_num, R7.Core.Certificates.Terminal109.positive_26⟩
theorem bound_9 : ordinaryBindings polynomial_9 witness_9 := by
 decide +kernel
theorem positive_9 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_9 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_9 ρ hρ u
def polynomial_10 : BiPoly := [[22888895004],[126616648500],[561086614068],[477230982000],[1788200079456],[473074290000],[1574041595088],[0],[25929764784]]
def witness_10 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_27, 45777790008, by norm_num, R7.Core.Certificates.Terminal109.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_28, 35338834712836733015088, by norm_num, R7.Core.Certificates.Terminal109.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_29, 115959949409056969519662205501664256, by norm_num, R7.Core.Certificates.Terminal109.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_30, 357142761567167054940796791381105355644949549056, by norm_num, R7.Core.Certificates.Terminal109.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_31, 18521255603489673903697731692107960747592416849137898487808, by norm_num, R7.Core.Certificates.Terminal109.positive_31⟩
theorem bound_10 : ordinaryBindings polynomial_10 witness_10 := by
 decide +kernel
theorem positive_10 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_10 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_10 ρ hρ u
def polynomial_11 : BiPoly := [[117073327224],[351130589250],[1940912894658],[1251680548500],[5658900507072],[1187148690000],[4722124785264],[0],[77789294352]]
def witness_11 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_0, 234146654448, by norm_num, R7.Core.Certificates.Terminal110.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_1, 785623831011256086715068, by norm_num, R7.Core.Certificates.Terminal110.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_2, 8524695645470496227618582682657921792, by norm_num, R7.Core.Certificates.Terminal110.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_3, 79402156230288166934570039345355491913438212146176, by norm_num, R7.Core.Certificates.Terminal110.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_4, 12353275406362753830911564630392159489068401578007013030395904, by norm_num, R7.Core.Certificates.Terminal110.positive_4⟩
theorem bound_11 : ordinaryBindings polynomial_11 witness_11 := by
 decide +kernel
theorem positive_11 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_11 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_11 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8001
