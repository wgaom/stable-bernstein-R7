import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal115
import R7.Certificates.Spectral.Terminal.Terminal116

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8008
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_48 : BiPoly := [[15992093848],[59023276500],[340516736844],[293715582000],[1293883523712],[365963130000],[1356354991512],[0],[25929764784]]
def witness_48 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_25, 31984187696, by norm_num, R7.Core.Certificates.Terminal115.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_26, 18298555280900417092848, by norm_num, R7.Core.Certificates.Terminal115.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal115.polynomial_27, 44593159501046333392871270723223552, by norm_num, R7.Core.Certificates.Terminal115.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal115.polynomial_28, 118517601513767335149401918373304806577276981248, by norm_num, R7.Core.Certificates.Terminal115.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal115.polynomial_29, 6146267060031658676252974483396323078570816485956437540864, by norm_num, R7.Core.Certificates.Terminal115.positive_29⟩
theorem bound_48 : ordinaryBindings polynomial_48 witness_48 := by
 decide +kernel
theorem positive_48 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_48 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_48 ρ hρ u
def polynomial_49 : BiPoly := [[109595502126],[307336674750],[2147102142792],[1479239644500],[7747693664400],[1832790960000],[7937188468848],[0],[155578588704]]
def witness_49 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_30, 219191004252, by norm_num, R7.Core.Certificates.Terminal115.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_31, 846795118174011878740668, by norm_num, R7.Core.Certificates.Terminal115.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_0, 12641795564539982904366663189624638400, by norm_num, R7.Core.Certificates.Terminal116.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_1, 197836139254504319768809608858217893741874529126400, by norm_num, R7.Core.Certificates.Terminal116.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal116.polynomial_2, 61558134679727593489405853008471593481760545817859708056371200, by norm_num, R7.Core.Certificates.Terminal116.positive_2⟩
theorem bound_49 : ordinaryBindings polynomial_49 witness_49 := by
 decide +kernel
theorem positive_49 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_49 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_49 ρ hρ u
def polynomial_50 : BiPoly := [[417229603155],[732932876250],[6541913774190],[3253679100000],[21562887808368],[3629878200000],[20345324872680],[0],[388946471760]]
def witness_50 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal116.polynomial_3, 834459206310, by norm_num, R7.Core.Certificates.Terminal116.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal116.polynomial_4, 10380729750429990112215300, by norm_num, R7.Core.Certificates.Terminal116.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_5, 438843079910688123244408490104715260800, by norm_num, R7.Core.Certificates.Terminal116.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_6, 17720033399165533212931544380239813599434825989888000, by norm_num, R7.Core.Certificates.Terminal116.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal116.polynomial_7, 13784288940149587742737641986204262724360482997672974075125760000, by norm_num, R7.Core.Certificates.Terminal116.positive_7⟩
theorem bound_50 : ordinaryBindings polynomial_50 witness_50 := by
 decide +kernel
theorem positive_50 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_50 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_50 ρ hρ u
def polynomial_51 : BiPoly := [[906431149930],[1040411985000],[11745394640340],[4060837935000],[34652285063712],[3748890600000],[29136514632480],[0],[518595295680]]
def witness_51 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal116.polynomial_8, 1812862299860, by norm_num, R7.Core.Certificates.Terminal116.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal116.polynomial_9, 41503109182368539639704800, by norm_num, R7.Core.Certificates.Terminal116.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_10, 2846460307783286508873050577477244435200, by norm_num, R7.Core.Certificates.Terminal116.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_11, 165288572619664684282593681976635625240740906350592000, by norm_num, R7.Core.Certificates.Terminal116.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal116.polynomial_12, 171435752380440318255971038363946477846687403022312895966085120000, by norm_num, R7.Core.Certificates.Terminal116.positive_12⟩
theorem bound_51 : ordinaryBindings polynomial_51 witness_51 := by
 decide +kernel
theorem positive_51 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_51 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_51 ρ hρ u
def polynomial_52 : BiPoly := [[1181122944645],[943036556250],[12803448011250],[3102156540000],[33187466553696],[2305865250000],[24364154477160],[0],[388946471760]]
def witness_52 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal116.polynomial_13, 2362245889290, by norm_num, R7.Core.Certificates.Terminal116.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal116.polynomial_14, 59600466920203216934962500, by norm_num, R7.Core.Certificates.Terminal116.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_15, 3933244226493677020128228431927992800000, by norm_num, R7.Core.Certificates.Terminal116.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_16, 191343443311508778657887048621607571608798238896000000, by norm_num, R7.Core.Certificates.Terminal116.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal116.polynomial_17, 148844714340841820122503911315947672553087243984601595153920000000, by norm_num, R7.Core.Certificates.Terminal116.positive_17⟩
theorem bound_52 : ordinaryBindings polynomial_52 witness_52 := by
 decide +kernel
theorem positive_52 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_52 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_52 ρ hρ u
def polynomial_53 : BiPoly := [[873488843616],[522171809250],[7943987961888],[1490698336500],[17694461970000],[916395480000],[11152252152432],[0],[155578588704]]
def witness_53 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal116.polynomial_18, 1746977687232, by norm_num, R7.Core.Certificates.Terminal116.positive_18⟩
 | 1 => ⟨R7.Core.Certificates.Terminal116.polynomial_19, 27483276035740476814865532, by norm_num, R7.Core.Certificates.Terminal116.positive_19⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_20, 968721463700179962204815599272004080000, by norm_num, R7.Core.Certificates.Terminal116.positive_20⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_21, 21583772133193304563771101217348742462263599045120000, by norm_num, R7.Core.Certificates.Terminal116.positive_21⟩
 | 4 => ⟨R7.Core.Certificates.Terminal116.polynomial_22, 6715945614781875673707100590990107425736257433342983236648960000, by norm_num, R7.Core.Certificates.Terminal116.positive_22⟩
theorem bound_53 : ordinaryBindings polynomial_53 witness_53 := by
 decide +kernel
theorem positive_53 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_53 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_53 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8008
