import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal113
import R7.Certificates.Spectral.Terminal.Terminal114

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8006
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_36 : BiPoly := [[457523961222],[-72186603750],[3989799974988],[-308895259500],[8720221117824],[-241000110000],[5525890706160],[0],[77789294352]]
def witness_36 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_29, 915047922444, by norm_num, R7.Core.Certificates.Terminal113.positive_29⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_30, 7296505450398825613598844, by norm_num, R7.Core.Certificates.Terminal113.positive_30⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_31, 127166971359762573386593410662817390912, by norm_num, R7.Core.Certificates.Terminal113.positive_31⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_0, 1404997781614928382664037851131553098417668492835840, by norm_num, R7.Core.Certificates.Terminal114.positive_0⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_1, 218587571995901355752904268653083880495459279653526721950351360, by norm_num, R7.Core.Certificates.Terminal114.positive_1⟩
theorem bound_36 : ordinaryBindings polynomial_36 witness_36 := by
 decide +kernel
theorem positive_36 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_36 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_36 ρ hρ u
def polynomial_37 : BiPoly := [[745667047674],[-232084664250],[5690091748020],[-608099989500],[10926584928576],[-348111270000],[6128715146832],[0],[77789294352]]
def witness_37 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal114.polynomial_2, 1491334095348, by norm_num, R7.Core.Certificates.Terminal114.positive_2⟩
 | 1 => ⟨R7.Core.Certificates.Terminal114.polynomial_3, 16917792367581018112359420, by norm_num, R7.Core.Certificates.Terminal114.positive_3⟩
 | 2 => ⟨R7.Core.Certificates.Terminal114.polynomial_4, 369155916347660100482560141834964571840, by norm_num, R7.Core.Certificates.Terminal114.positive_4⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_5, 4522852789408600735062221393084821928775289224821760, by norm_num, R7.Core.Certificates.Terminal114.positive_5⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_6, 703659053892139821160397413963333420642010704747187586749399040, by norm_num, R7.Core.Certificates.Terminal114.positive_6⟩
theorem bound_37 : ordinaryBindings polynomial_37 witness_37 := by
 decide +kernel
theorem positive_37 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_37 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_37 ρ hρ u
def polynomial_38 : BiPoly := [[100265917408],[-30969769500],[802279483800],[-109228977000],[1664087526768],[-71407440000],[987962277768],[0],[12964882392]]
def witness_38 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal114.polynomial_7, 200531834816, by norm_num, R7.Core.Certificates.Terminal114.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal114.polynomial_8, 320806027220411565711600, by norm_num, R7.Core.Certificates.Terminal114.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal114.polynomial_9, 1065306077630747122080337038272217600, by norm_num, R7.Core.Certificates.Terminal114.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_10, 2103328640805458069434017629946725360897076633600, by norm_num, R7.Core.Certificates.Terminal114.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_11, 54538816919535952043798817152627743059108708342470551142400, by norm_num, R7.Core.Certificates.Terminal114.positive_11⟩
theorem bound_38 : ordinaryBindings polynomial_38 witness_38 := by
 decide +kernel
theorem positive_38 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_38 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_38 ρ hρ u
def polynomial_39 : BiPoly := [[291162947872],[-160275274500],[2183283241584],[-381224694000],[4050202812336],[-196370460000],[2160120912408],[0],[25929764784]]
def witness_39 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal114.polynomial_12, 582325895744, by norm_num, R7.Core.Certificates.Terminal114.positive_12⟩
 | 1 => ⟨R7.Core.Certificates.Terminal114.polynomial_13, 2517076575020483148586992, by norm_num, R7.Core.Certificates.Terminal114.positive_13⟩
 | 2 => ⟨R7.Core.Certificates.Terminal114.polynomial_14, 20304710503281112017181405240709466624, by norm_num, R7.Core.Certificates.Terminal114.positive_14⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_15, 87624197667238988677483600787255316493848606941184, by norm_num, R7.Core.Certificates.Terminal114.positive_15⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_16, 4544149669796456958242378010861775163277939921781941684928512, by norm_num, R7.Core.Certificates.Terminal114.positive_16⟩
theorem bound_39 : ordinaryBindings polynomial_39 witness_39 := by
 decide +kernel
theorem positive_39 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_39 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_39 ρ hρ u
def polynomial_40 : BiPoly := [[54542008704],[-36944430000],[394572502224],[-77713062000],[681747224448],[-35703720000],[334902467040],[0],[3704252112]]
def witness_40 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal114.polynomial_17, 109084017408, by norm_num, R7.Core.Certificates.Terminal114.positive_17⟩
 | 1 => ⟨R7.Core.Certificates.Terminal114.polynomial_18, 84718216494616969430784, by norm_num, R7.Core.Certificates.Terminal114.positive_18⟩
 | 2 => ⟨R7.Core.Certificates.Terminal114.polynomial_19, 114854024622176517103461496545214464, by norm_num, R7.Core.Certificates.Terminal114.positive_19⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_20, 76821797368131003293875056291677888493382533120, by norm_num, R7.Core.Certificates.Terminal114.positive_20⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_21, 569134610297070620888031267865133412950625492667339898880, by norm_num, R7.Core.Certificates.Terminal114.positive_21⟩
theorem bound_40 : ordinaryBindings polynomial_40 witness_40 := by
 decide +kernel
theorem positive_40 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_40 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_40 ρ hρ u
def polynomial_41 : BiPoly := [[985257308],[13277269500],[57184782984],[62395236000],[224689343520],[68432130000],[217686603576],[0],[3704252112]]
def witness_41 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal114.polynomial_22, 1970514616, by norm_num, R7.Core.Certificates.Terminal114.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal114.polynomial_23, 49081015989889938288, by norm_num, R7.Core.Certificates.Terminal114.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal114.polynomial_24, 14384423052155127568875329387520, by norm_num, R7.Core.Certificates.Terminal114.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal114.polynomial_25, 6032748138497749383156317353077751043543040, by norm_num, R7.Core.Certificates.Terminal114.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal114.polynomial_26, 44693640066388713319606971562561018006509019765800960, by norm_num, R7.Core.Certificates.Terminal114.positive_26⟩
theorem bound_41 : ordinaryBindings polynomial_41 witness_41 := by
 decide +kernel
theorem positive_41 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_41 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_41 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8006
