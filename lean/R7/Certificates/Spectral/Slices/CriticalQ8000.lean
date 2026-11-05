import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal108
import R7.Certificates.Spectral.Terminal.Terminal109

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8000
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_0 : BiPoly := [[492628654],[4828098000],[16338509424],[14681232000],[44937868704],[11901240000],[33490246704],[0],[463031514]]
def witness_0 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal108.polynomial_9, 985257308, by norm_num, R7.Core.Certificates.Terminal108.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal108.polynomial_10, 8884741326041741184, by norm_num, R7.Core.Certificates.Terminal108.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal108.polynomial_11, 586161724115925386282491011072, by norm_num, R7.Core.Certificates.Terminal108.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal108.polynomial_12, 38002971058840691587860399340408951013376, by norm_num, R7.Core.Certificates.Terminal108.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal108.polynomial_13, 35193146451746377021468129454468315933750647062528, by norm_num, R7.Core.Certificates.Terminal108.positive_13⟩
theorem bound_0 : ordinaryBindings polynomial_0 witness_0 := by
 decide +kernel
theorem positive_0 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_0 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_0 ρ hρ u
def polynomial_1 : BiPoly := [[2955771924],[30175612500],[106200311256],[99098316000],[314565080928],[86283990000],[251176850280],[0],[3704252112]]
def witness_1 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal108.polynomial_14, 5911543848, by norm_num, R7.Core.Certificates.Terminal108.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal108.polynomial_15, 345048003572027656176, by norm_num, R7.Core.Certificates.Terminal108.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal108.polynomial_16, 159025930469614552735901310022656, by norm_num, R7.Core.Certificates.Terminal108.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal108.polynomial_17, 77318407482361554445596406184411121439887360, by norm_num, R7.Core.Certificates.Terminal108.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal108.polynomial_18, 572813748426028781605406953416429516139982468644208640, by norm_num, R7.Core.Certificates.Terminal108.positive_18⟩
theorem bound_1 : ordinaryBindings polynomial_1 witness_1 := by
 decide +kernel
theorem positive_1 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_1 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_1 ρ hρ u
def polynomial_2 : BiPoly := [[17166671253],[88625607750],[375884059635],[294610423500],[1071522847368],[261827280000],[854001290952],[0],[12964882392]]
def witness_2 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal108.polynomial_19, 34333342506, by norm_num, R7.Core.Certificates.Terminal108.positive_19⟩
 | 1 => ⟨R7.Core.Certificates.Terminal108.polynomial_20, 17956213974931508628120, by norm_num, R7.Core.Certificates.Terminal108.positive_20⟩
 | 2 => ⟨R7.Core.Certificates.Terminal108.polynomial_21, 35501014233794502439454511927076320, by norm_num, R7.Core.Certificates.Terminal108.positive_21⟩
 | 3 => ⟨R7.Core.Certificates.Terminal108.polynomial_22, 59404862215936669255440482139894458118058913280, by norm_num, R7.Core.Certificates.Terminal108.positive_22⟩
 | 4 => ⟨R7.Core.Certificates.Terminal108.polynomial_23, 1540354104285166850033976114199016281586406924005053931520, by norm_num, R7.Core.Certificates.Terminal108.positive_23⟩
theorem bound_2 : ordinaryBindings polynomial_2 witness_2 := by
 decide +kernel
theorem positive_2 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_2 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_2 ρ hρ u
def polynomial_3 : BiPoly := [[58536663612],[165018945750],[875115694728],[520743604500],[2294853163440],[437370570000],[1724747705256],[0],[25929764784]]
def witness_3 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal108.polynomial_24, 117073327224, by norm_num, R7.Core.Certificates.Terminal108.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal108.polynomial_25, 177674159719057028287644, by norm_num, R7.Core.Certificates.Terminal108.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal108.polynomial_26, 783724984065780748036466985443070720, by norm_num, R7.Core.Certificates.Terminal108.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal108.polynomial_27, 2669467909849036428680239875467189946756647408640, by norm_num, R7.Core.Certificates.Terminal108.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal108.polynomial_28, 138437350001643263089452023039123374857698701988916658667520, by norm_num, R7.Core.Certificates.Terminal108.positive_28⟩
theorem bound_3 : ordinaryBindings polynomial_3 witness_3 := by
 decide +kernel
theorem positive_3 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_3 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_3 ρ hρ u
def polynomial_4 : BiPoly := [[125008747455],[210469863750],[1400592958110],[606964950000],[3310487998584],[446296500000],[2260591652520],[0],[32412205980]]
def witness_4 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal108.polynomial_29, 250017494910, by norm_num, R7.Core.Certificates.Terminal108.positive_29⟩
 | 1 => ⟨R7.Core.Certificates.Terminal108.polynomial_30, 656047922003553972377700, by norm_num, R7.Core.Certificates.Terminal108.positive_30⟩
 | 2 => ⟨R7.Core.Certificates.Terminal108.polynomial_31, 4251569486707654010099677510426353600, by norm_num, R7.Core.Certificates.Terminal108.positive_31⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_0, 19091452987149903976573342715725523603763702144000, by norm_num, R7.Core.Certificates.Terminal109.positive_0⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_1, 1237592213353977961651832557358456512377082034277391242240000, by norm_num, R7.Core.Certificates.Terminal109.positive_1⟩
theorem bound_4 : ordinaryBindings polynomial_4 witness_4 := by
 decide +kernel
theorem positive_4 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_4 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_4 ρ hρ u
def polynomial_5 : BiPoly := [[172157607918],[191012267250],[1542333947508],[481021389000],[3230620122240],[294555690000],[1959179432184],[0],[25929764784]]
def witness_5 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_2, 344315215836, by norm_num, R7.Core.Certificates.Terminal109.positive_2⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_3, 1025612405814828406110876, by norm_num, R7.Core.Certificates.Terminal109.positive_3⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_4, 6547059954175227775418057084870964480, by norm_num, R7.Core.Certificates.Terminal109.positive_4⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_5, 25564745141918000082967492968654489037206065648640, by norm_num, R7.Core.Certificates.Terminal109.positive_5⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_6, 1325775656585680881534079154790769571400919813614595178987520, by norm_num, R7.Core.Certificates.Terminal109.positive_6⟩
theorem bound_5 : ordinaryBindings polynomial_5 witness_5 := by
 decide +kernel
theorem positive_5 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_5 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_5 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8000
