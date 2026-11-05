import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal112

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8004
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_24 : BiPoly := [[41079480388],[75619309500],[610495513872],[270176877000],[1750941404640],[261827280000],[1473570854976],[0],[25929764784]]
def witness_24 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_1, 82158960776, by norm_num, R7.Core.Certificates.Terminal112.positive_1⟩
 | 1 => ⟨R7.Core.Certificates.Terminal112.polynomial_2, 94597073987010433519344, by norm_num, R7.Core.Certificates.Terminal112.positive_2⟩
 | 2 => ⟨R7.Core.Certificates.Terminal112.polynomial_3, 325270629095874952159198055838712320, by norm_num, R7.Core.Certificates.Terminal112.positive_3⟩
 | 3 => ⟨R7.Core.Certificates.Terminal112.polynomial_4, 952133675196645021913197617268592478433009008640, by norm_num, R7.Core.Certificates.Terminal112.positive_4⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_5, 49377204481548920728307479762167719033039032990776447467520, by norm_num, R7.Core.Certificates.Terminal112.positive_5⟩
theorem bound_24 : ordinaryBindings polynomial_24 witness_24 := by
 decide +kernel
theorem positive_24 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_24 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_24 ρ hρ u
def polynomial_25 : BiPoly := [[273349707230],[310782978750],[3425527640040],[1080085492500],[9389880904128],[952099200000],[7535305508400],[0],[129648823920]]
def witness_25 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_6, 546699414460, by norm_num, R7.Core.Certificates.Terminal112.positive_6⟩
 | 1 => ⟨R7.Core.Certificates.Terminal112.polynomial_7, 3648881850172104350394300, by norm_num, R7.Core.Certificates.Terminal112.positive_7⟩
 | 2 => ⟨R7.Core.Certificates.Terminal112.polynomial_8, 67887360856087293018312571481220340800, by norm_num, R7.Core.Certificates.Terminal112.positive_8⟩
 | 3 => ⟨R7.Core.Certificates.Terminal112.polynomial_9, 1019796322977853087366494822734830358016730525440000, by norm_num, R7.Core.Certificates.Terminal112.positive_9⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_10, 264430787824038249967214127560679267875163312613719281049600000, by norm_num, R7.Core.Certificates.Terminal112.positive_10⟩
theorem bound_25 : ordinaryBindings polynomial_25 witness_25 := by
 decide +kernel
theorem positive_25 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_25 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_25 ρ hρ u
def polynomial_26 : BiPoly := [[822127921920],[568542150000],[8773828149840],[1724404695000],[21906285099936],[1279383300000],[16075318417920],[0],[259297647840]]
def witness_26 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_11, 1644255843840, by norm_num, R7.Core.Certificates.Terminal112.positive_11⟩
 | 1 => ⟨R7.Core.Certificates.Terminal112.polynomial_12, 28529596240118007821971200, by norm_num, R7.Core.Certificates.Terminal112.positive_12⟩
 | 2 => ⟨R7.Core.Certificates.Terminal112.polynomial_13, 1245065625642495129175289596161027686400, by norm_num, R7.Core.Certificates.Terminal112.positive_13⟩
 | 3 => ⟨R7.Core.Certificates.Terminal112.polynomial_14, 39982954906646749127490557905366792590633931800576000, by norm_num, R7.Core.Certificates.Terminal112.positive_14⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_15, 20734972321972577661081747893341853262393037060760665514311680000, by norm_num, R7.Core.Certificates.Terminal112.positive_15⟩
theorem bound_26 : ordinaryBindings polynomial_26 witness_26 := by
 decide +kernel
theorem positive_26 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_26 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_26 ρ hρ u
def polynomial_27 : BiPoly := [[1376604223140],[580026495000],[12299692502580],[1429034107500],[27248486871072],[862839900000],[17749830753120],[0],[259297647840]]
def witness_27 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_16, 2753208446280, by norm_num, R7.Core.Certificates.Terminal112.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal112.polynomial_17, 67390803834598108357804800, by norm_num, R7.Core.Certificates.Terminal112.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal112.polynomial_18, 3666972434123364234922938159841835491200, by norm_num, R7.Core.Certificates.Terminal112.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal112.polynomial_19, 130126108203059975718005822697168327862051282265088000, by norm_num, R7.Core.Certificates.Terminal112.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_20, 67482787559253561588252849921599664086351666977586451501219840000, by norm_num, R7.Core.Certificates.Terminal112.positive_20⟩
theorem bound_27 : ordinaryBindings polynomial_27 witness_27 := by
 decide +kernel
theorem positive_27 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_27 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_27 ρ hρ u
def polynomial_28 : BiPoly := [[1242778412790],[340131371250],[9287374125300],[746069415000],[17762686510464],[386790300000],[10047074011200],[0],[129648823920]]
def witness_28 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_21, 2485556825580, by norm_num, R7.Core.Certificates.Terminal112.positive_21⟩
 | 1 => ⟨R7.Core.Certificates.Terminal112.polynomial_22, 46052902948000589003785500, by norm_num, R7.Core.Certificates.Terminal112.positive_22⟩
 | 2 => ⟨R7.Core.Certificates.Terminal112.polynomial_23, 1634663046347883535161458594047222944000, by norm_num, R7.Core.Certificates.Terminal112.positive_23⟩
 | 3 => ⟨R7.Core.Certificates.Terminal112.polynomial_24, 32840271395560290984768992809434692314694505945600000, by norm_num, R7.Core.Certificates.Terminal112.positive_24⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_25, 8515405127296017671256557101252289077294410459864974997504000000, by norm_num, R7.Core.Certificates.Terminal112.positive_25⟩
theorem bound_28 : ordinaryBindings polynomial_28 witness_28 := by
 decide +kernel
theorem positive_28 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_28 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_28 ρ hρ u
def polynomial_29 : BiPoly := [[497111365116],[127159119000],[2995493174664],[246212619000],[4781545239840],[113061780000],[2310827022576],[0],[25929764784]]
def witness_29 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_26, 994222730232, by norm_num, R7.Core.Certificates.Terminal112.positive_26⟩
 | 1 => ⟨R7.Core.Certificates.Terminal112.polynomial_27, 5940205363466670497484096, by norm_num, R7.Core.Certificates.Terminal112.positive_27⟩
 | 2 => ⟨R7.Core.Certificates.Terminal112.polynomial_28, 56746450926827605782446235634459169280, by norm_num, R7.Core.Certificates.Terminal112.positive_28⟩
 | 3 => ⟨R7.Core.Certificates.Terminal112.polynomial_29, 262186531030223227563189200551875712911323131330560, by norm_num, R7.Core.Certificates.Terminal112.positive_29⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_30, 13596870158293210971453602934398280451585841291239523501998080, by norm_num, R7.Core.Certificates.Terminal112.positive_30⟩
theorem bound_29 : ordinaryBindings polynomial_29 witness_29 := by
 decide +kernel
theorem positive_29 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_29 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_29 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8004
