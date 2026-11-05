import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal118
import R7.Certificates.Spectral.Terminal.Terminal119

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8011
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_66 : BiPoly := [[10269870097],[21032235750],[155314182411],[111095023500],[577206291624],[154716120000],[636314687376],[0],[12964882392]]
def witness_66 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_19, 20539740194, by norm_num, R7.Core.Certificates.Terminal118.positive_19⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_20, 5937870969687350992968, by norm_num, R7.Core.Certificates.Terminal118.positive_20⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_21, 6601249350440414976716534626100064, by norm_num, R7.Core.Certificates.Terminal118.positive_21⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_22, 8258808554137382890905032520463674689307184128, by norm_num, R7.Core.Certificates.Terminal118.positive_22⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_23, 214148963204869468382513426137493751310029564360418148352, by norm_num, R7.Core.Certificates.Terminal118.positive_23⟩
theorem bound_66 : ordinaryBindings polynomial_66 witness_66 := by
 decide +kernel
theorem positive_66 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_66 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_66 ρ hρ u
def polynomial_67 : BiPoly := [[51058838514],[100132333500],[890623437660],[538109361000],[3314452140576],[770605290000],[3667182014088],[0],[77789294352]]
def witness_67 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_24, 102117677028, by norm_num, R7.Core.Certificates.Terminal118.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_25, 171870308908906721898960, by norm_num, R7.Core.Certificates.Terminal118.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_26, 1109742459962351630985432705188401920, by norm_num, R7.Core.Certificates.Terminal118.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_27, 8037193001442081962943935576057953394431292497920, by norm_num, R7.Core.Certificates.Terminal118.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_28, 1250415144306024948590311521998593640820226739521016455495680, by norm_num, R7.Core.Certificates.Terminal118.positive_28⟩
theorem bound_67 : ordinaryBindings polynomial_67 witness_67 := by
 decide +kernel
theorem positive_67 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_67 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_67 ρ hρ u
def polynomial_68 : BiPoly := [[167212108245],[210252296250],[2562540984120],[1108098405000],[8970081698016],[1487655000000],[9293543460360],[0],[194473235880]]
def witness_68 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_29, 334424216490, by norm_num, R7.Core.Certificates.Terminal118.positive_29⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_30, 1669745493597291300215100, by norm_num, R7.Core.Certificates.Terminal118.positive_30⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_31, 29544873483994826105491051295836483200, by norm_num, R7.Core.Certificates.Terminal118.positive_31⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_0, 545457788704863618448406231978814626778522011904000, by norm_num, R7.Core.Certificates.Terminal119.positive_0⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_1, 212153882410768284347494449523356032152587351477557519831040000, by norm_num, R7.Core.Certificates.Terminal119.positive_1⟩
theorem bound_68 : ordinaryBindings polynomial_68 witness_68 := by
 decide +kernel
theorem positive_68 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_68 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_68 ρ hρ u
def polynomial_69 : BiPoly := [[332572456870],[258732412500],[4440282758820],[1271774565000],[14190055481376],[1457901900000],[13228647448080],[0],[259297647840]]
def witness_69 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_2, 665144913740, by norm_num, R7.Core.Certificates.Terminal119.positive_2⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_3, 5839920523915006092123600, by norm_num, R7.Core.Certificates.Terminal119.positive_3⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_4, 164661780085469270505593039348680147200, by norm_num, R7.Core.Certificates.Terminal119.positive_4⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_5, 4344092651544434785479651128925402270950877514752000, by norm_num, R7.Core.Certificates.Terminal119.positive_5⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_6, 2252826013089001366234297047828314791366713799518277001871360000, by norm_num, R7.Core.Certificates.Terminal119.positive_6⟩
theorem bound_69 : ordinaryBindings polynomial_69 witness_69 := by
 decide +kernel
theorem positive_69 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_69 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_69 ρ hρ u
def polynomial_70 : BiPoly := [[416951021955],[200523258750],[4740298614105],[881401522500],[13505730499656],[833086800000],[11051781412320],[0],[194473235880]]
def witness_70 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_7, 833902043910, by norm_num, R7.Core.Certificates.Terminal119.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_8, 7865679828792080259138600, by norm_num, R7.Core.Certificates.Terminal119.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_9, 211815671578523486738209235121875143200, by norm_num, R7.Core.Certificates.Terminal119.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_10, 4676421957762703314887406056776816349219196488448000, by norm_num, R7.Core.Certificates.Terminal119.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_11, 1818877820932795197645112867441796956794290505044031198228480000, by norm_num, R7.Core.Certificates.Terminal119.positive_11⟩
theorem bound_70 : ordinaryBindings polynomial_70 witness_70 := by
 decide +kernel
theorem positive_70 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_70 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_70 ρ hρ u
def polynomial_71 : BiPoly := [[40498456446],[74071252500],[849361780854],[409648581000],[3165666531408],[612913860000],[3516475903920],[0],[77789294352]]
def witness_71 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_12, 80996912892, by norm_num, R7.Core.Certificates.Terminal119.positive_12⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_13, 132104813908332106489536, by norm_num, R7.Core.Certificates.Terminal119.positive_13⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_14, 822807325355481583045319704322693376, by norm_num, R7.Core.Certificates.Terminal119.positive_14⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_15, 5737137322842707844099752942534552203691592867840, by norm_num, R7.Core.Certificates.Terminal119.positive_15⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_16, 892575727888913307762830016194596844606951157248299188879360, by norm_num, R7.Core.Certificates.Terminal119.positive_16⟩
theorem bound_71 : ordinaryBindings polynomial_71 witness_71 := by
 decide +kernel
theorem positive_71 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_71 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_71 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8011
