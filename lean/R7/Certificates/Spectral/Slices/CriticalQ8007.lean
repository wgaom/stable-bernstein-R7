import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal114
import R7.Certificates.Spectral.Terminal.Terminal115

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8007
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_42 : BiPoly := [[11444447502],[75982081500],[370405108866],[365241117000],[1433354464176],[422494020000],[1440080608272],[0],[25929764784]]
def witness_42 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal114.polynomial_27, 22888895004, by norm_num, R7.Core.Certificates.Terminal114.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal114.polynomial_28, 11183050582485484760928, by norm_num, R7.Core.Certificates.Terminal114.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal114.polynomial_29, 29005147785175676989691848045030656, by norm_num, R7.Core.Certificates.Terminal114.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_30, 81543313816623273438637388529087192627534372864, by norm_num, R7.Core.Certificates.Terminal114.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_31, 4228797893945877578807964684054501294117730420476944842752, by norm_num, R7.Core.Certificates.Terminal114.positive_31⟩
theorem bound_42 : ordinaryBindings polynomial_42 witness_42 := by
 decide +kernel
theorem positive_42 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_42 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_42 ρ hρ u
def polynomial_43 : BiPoly := [[58536663612],[207204341250],[1256478705132],[941130283500],[4433241523824],[1062185670000],[4270006454760],[0],[77789294352]]
def witness_43 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_0, 117073327224, by norm_num, R7.Core.Certificates.Terminal115.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_1, 251266646158966436664636, by norm_num, R7.Core.Certificates.Terminal115.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal115.polynomial_2, 2124156544132670361734471550250576128, by norm_num, R7.Core.Certificates.Terminal115.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal115.polynomial_3, 17856835630513397878865011007441299524437135938560, by norm_num, R7.Core.Certificates.Terminal115.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal115.polynomial_4, 2778141286114576440957445561863142622135675969288963254026240, by norm_num, R7.Core.Certificates.Terminal115.positive_4⟩
theorem bound_43 : ordinaryBindings polynomial_43 witness_43 := by
 decide +kernel
theorem positive_43 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_43 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_43 ρ hρ u
def polynomial_44 : BiPoly := [[166678329940],[348453720000],[2652915193380],[1430387130000],[8395204073568],[1428148800000],[7367854274880],[0],[129648823920]]
def witness_44 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_5, 333356659880, by norm_num, R7.Core.Certificates.Terminal115.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_6, 1647313900638283775188800, by norm_num, R7.Core.Certificates.Terminal115.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal115.polynomial_7, 26977022564658474990118353004579276800, by norm_num, R7.Core.Certificates.Terminal115.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal115.polynomial_8, 394165665803872419199113889478487689701477613568000, by norm_num, R7.Core.Certificates.Terminal115.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal115.polynomial_9, 102206230002231641061780688154045582219988936970598869893120000, by norm_num, R7.Core.Certificates.Terminal115.positive_9⟩
theorem bound_44 : ordinaryBindings polynomial_44 witness_44 := by
 decide +kernel
theorem positive_44 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_44 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_44 ρ hρ u
def polynomial_45 : BiPoly := [[286929346530],[390839786250],[3652555940760],[1394531685000],[10231114791168],[1145494350000],[7953933592200],[0],[129648823920]]
def witness_45 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_10, 573858693060, by norm_num, R7.Core.Certificates.Terminal115.positive_10⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_11, 4039346218470199077188700, by norm_num, R7.Core.Certificates.Terminal115.positive_11⟩
 | 2 => ⟨R7.Core.Certificates.Terminal115.polynomial_12, 81538035998966211044102636147558803200, by norm_num, R7.Core.Certificates.Terminal115.positive_12⟩
 | 3 => ⟨R7.Core.Certificates.Terminal115.polynomial_13, 1291795989496828273033588991003178470318867710080000, by norm_num, R7.Core.Certificates.Terminal115.positive_13⟩
 | 4 => ⟨R7.Core.Certificates.Terminal115.polynomial_14, 334959661565672916338018926680443099317411651995871058227200000, by norm_num, R7.Core.Certificates.Terminal115.positive_14⟩
theorem bound_45 : ordinaryBindings polynomial_45 witness_45 := by
 decide +kernel
theorem positive_45 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_45 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_45 ρ hρ u
def polynomial_46 : BiPoly := [[305668769076],[297005319000],[3225259758858],[888302007000],[7872694421616],[589111380000],[5324949225936],[0],[77789294352]]
def witness_46 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_15, 611337538152, by norm_num, R7.Core.Certificates.Terminal115.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_16, 3855232562247634028900832, by norm_num, R7.Core.Certificates.Terminal115.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal115.polynomial_17, 60219741270523658337752232795474369024, by norm_num, R7.Core.Certificates.Terminal115.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal115.polynomial_18, 639996162317273000778389517855283738456892831612928, by norm_num, R7.Core.Certificates.Terminal115.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal115.polynomial_19, 99569699709297439742984934649912052938604437483313654241165312, by norm_num, R7.Core.Certificates.Terminal115.positive_19⟩
theorem bound_46 : ordinaryBindings polynomial_46 witness_46 := by
 decide +kernel
theorem positive_46 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_46 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_46 ρ hρ u
def polynomial_47 : BiPoly := [[190897030464],[142236055500],[1676933134452],[363586111500],[3493954525296],[199345770000],[2026159925592],[0],[25929764784]]
def witness_47 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal115.polynomial_20, 381794060928, by norm_num, R7.Core.Certificates.Terminal115.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal115.polynomial_21, 1260255127130098727532912, by norm_num, R7.Core.Certificates.Terminal115.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal115.polynomial_22, 8756076996312564248828415228225083904, by norm_num, R7.Core.Certificates.Terminal115.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal115.polynomial_23, 35432343684842017278737339977918058673188393742336, by norm_num, R7.Core.Certificates.Terminal115.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal115.polynomial_24, 1837504674987602668475445980290510030843372354115099965390848, by norm_num, R7.Core.Certificates.Terminal115.positive_24⟩
theorem bound_47 : ordinaryBindings polynomial_47 witness_47 := by
 decide +kernel
theorem positive_47 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_47 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_47 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8007
