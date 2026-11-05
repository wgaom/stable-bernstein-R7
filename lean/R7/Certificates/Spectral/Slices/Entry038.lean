import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal057

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry038
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_228 : BiPoly := [[28079108707318272,1197090972277842155,2905363371240864480],[0,257849784318788200,735938187432840000],[362872408655051676,23061919841731899140,63896076432534098340],[0,2700551766356931900,6488877511972485000],[1944967597211595600,213690837825065900625,389197933734566416500],[0,5782921324179552000,20871205477582950000],[5432425284321325800,731506328916226821000,994181622196112622000],[0,-375364611621027000,28169373665808900000],[8268278047406475840,1027454183500146066000,1111426153590990585600],[0,-3243534014209406400,12445814440659600000],[6385556657243399832,538398860112155432880,424352732230279424880],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_228 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_0, 2300, by norm_num, R7.Core.Certificates.Terminal057.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_1, 901600, by norm_num, R7.Core.Certificates.Terminal057.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_2, 6272, by norm_num, R7.Core.Certificates.Terminal057.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_3, 1128960000, by norm_num, R7.Core.Certificates.Terminal057.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_4, 213373440000000, by norm_num, R7.Core.Certificates.Terminal057.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_5, 96786192384000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_6, 3598752520889126092800000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_6⟩
theorem bound_228 : minorBindings polynomial_228 witness_228 := by
 decide +kernel
theorem positive_228 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_228 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_228 ρ hρ u
def polynomial_229 : BiPoly := [[177566651779436064,7540339336908451610,18860893854274385760],[0,0,0],[2300836802284055016,149539939023106664240,412217292436678486440],[0,0,0],[12203398787949613440,1352636936514919420500,2463051023686299459600],[0,0,0],[33744543788232943200,4558029079158398934000,6202695125805833088000],[0,0,0],[50811793816153980960,6320972473439992704000,6839900088725960726400],[0,0,0],[38801407968217856304,3271544665904434923360,2578550997119022747360],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
def witness_229 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_8, 4600, by norm_num, R7.Core.Certificates.Terminal057.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_9, 3606400, by norm_num, R7.Core.Certificates.Terminal057.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_10, 50176, by norm_num, R7.Core.Certificates.Terminal057.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_11, 54190080000, by norm_num, R7.Core.Certificates.Terminal057.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_12, 54623600640000000, by norm_num, R7.Core.Certificates.Terminal057.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_13, 23637511048790016000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_14, 5273410413969755585327923200000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_14⟩
theorem bound_229 : minorBindings polynomial_229 witness_229 := by
 decide +kernel
theorem positive_229 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_229 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_229 ρ hρ u
def polynomial_230 : BiPoly := [[4694723860492656,210341023068731190,507696739629899040],[0,0,0],[59234855190714216,3793728474577099740,10465716871812439440],[0,0,0],[318730292108497080,35140751116818066000,64002037944348862200],[0,0,0],[892531168356110400,120353694734337678000,163690838663857461000],[0,0,0],[1363386273774472080,169579076698618587000,183492144053468107200],[0,0,0],[1057480720307824176,89161594668255039840,70274974764250095840],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
def witness_230 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_16, 13800, by norm_num, R7.Core.Certificates.Terminal057.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_17, 16228800, by norm_num, R7.Core.Certificates.Terminal057.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_18, 169344, by norm_num, R7.Core.Certificates.Terminal057.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_19, 91445760000, by norm_num, R7.Core.Certificates.Terminal057.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_20, 69132994560000000, by norm_num, R7.Core.Certificates.Terminal057.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_21, 815326884642816000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_22, 5052648539328333034291200000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_22⟩
theorem bound_230 : minorBindings polynomial_230 witness_230 := by
 decide +kernel
theorem positive_230 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_230 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_230 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry038
