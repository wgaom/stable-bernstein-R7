import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal107
import R7.Certificates.Spectral.Terminal.Terminal108

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL038
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_228 : BiPoly := [[282206027536452271],[52633269347645000],[5180295548758634668],[549437690762047500],[45753563943205448925],[1186325372068200000],[154346281401152489400],[-35709289082775000],[216779696269937655120],[-631505308641480000],[115477039291789850976],[0],[475669541458032768]]
def witness_228 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal107.polynomial_20, 28220602753645227100, by norm_num, R7.Core.Certificates.Terminal107.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal107.polynomial_21, 14319798504537861388388679763115224074400, by norm_num, R7.Core.Certificates.Terminal107.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal107.polynomial_22, 65484008944862623824187370438029794688296695971747487321688064, by norm_num, R7.Core.Certificates.Terminal107.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal107.polynomial_23, 1010670944126475755852509039971377804638679066528222600602239144447368948386652160000, by norm_num, R7.Core.Certificates.Terminal107.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal107.polynomial_24, 21909293820903474820902524864192900790359162952407518982067472551594295939184246081403412708148305920000000, by norm_num, R7.Core.Certificates.Terminal107.positive_24⟩
 | 5 => ⟨R7.Core.Certificates.Terminal107.polynomial_25, 253001030704893397635013981925446491176344200813124029049917841539156631141757383805218210382674267025238115542205857792000000000, by norm_num, R7.Core.Certificates.Terminal107.positive_25⟩
 | 6 => ⟨R7.Core.Certificates.Terminal107.polynomial_26, 12034488426380631130759290037474953653792642204817904409342813552568764739507133283540311442631057269398908360360696642433228334228412825600000000000, by norm_num, R7.Core.Certificates.Terminal107.positive_26⟩
theorem bound_228 : minorBindings polynomial_228 witness_228 := by
 decide +kernel
theorem positive_228 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_228 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_228 ρ hρ u
def polynomial_229 : BiPoly := [[1779347765126848402],[0],[33518439693147412288],[0],[289473009657706764420],[0],[961609542361493727600],[0],[1333579361441853617280],[0],[701688506269856801472],[0],[2854017248748196608]]
def witness_229 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal107.polynomial_27, 177934776512684840200, by norm_num, R7.Core.Certificates.Terminal107.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal107.polynomial_28, 584481415433700764951395468007846045004800, by norm_num, R7.Core.Certificates.Terminal107.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal107.polynomial_29, 16915469007339467587766931222768438660552827728443945641979756544, by norm_num, R7.Core.Certificates.Terminal107.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal107.polynomial_30, 1626607641097773601116181943277310640016068702178907571373289212131838008483105341440000, by norm_num, R7.Core.Certificates.Terminal107.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal107.polynomial_31, 216921037933160872761352605848317100629082941402517874009279824811303759466046608483649344072255348408320000000, by norm_num, R7.Core.Certificates.Terminal107.positive_31⟩
 | 5 => ⟨R7.Core.Certificates.Terminal108.polynomial_0, 15221099908582659813419877938311107154527204327258339327934886557523920126171254091297501402021188347651317034863420143304704000000000, by norm_num, R7.Core.Certificates.Terminal108.positive_0⟩
 | 6 => ⟨R7.Core.Certificates.Terminal108.polynomial_1, 4344128168401450966284744966201324536221524605695732311514050588097049397987128929561790003888756647352097657325825858547968563003404544324403200000000000, by norm_num, R7.Core.Certificates.Terminal108.positive_1⟩
theorem bound_229 : minorBindings polynomial_229 witness_229 := by
 decide +kernel
theorem positive_229 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_229 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_229 ρ hρ u
def polynomial_230 : BiPoly := [[49256495362758558],[0],[851506607203115388],[0],[7522582264424317440],[0],[25392910414778737200],[0],[35777516716425952440],[0],[19123586124755007168],[0],[79278256909672128]]
def witness_230 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal108.polynomial_2, 4925649536275855800, by norm_num, R7.Core.Certificates.Terminal108.positive_2⟩
 | 1 => ⟨R7.Core.Certificates.Terminal108.polynomial_3, 411033866240773555289212190333206939200, by norm_num, R7.Core.Certificates.Terminal108.positive_3⟩
 | 2 => ⟨R7.Core.Certificates.Terminal108.polynomial_4, 309143102382516514560015304082849478834352928042111139874944, by norm_num, R7.Core.Certificates.Terminal108.positive_4⟩
 | 3 => ⟨R7.Core.Certificates.Terminal108.polynomial_5, 785004310414601304804666948254699079974593981860083985727119126642183824071680000, by norm_num, R7.Core.Certificates.Terminal108.positive_5⟩
 | 4 => ⟨R7.Core.Certificates.Terminal108.polynomial_6, 2808550483832482557455599969340393496933729985589308901709852848028944428263324158899474283089920000000, by norm_num, R7.Core.Certificates.Terminal108.positive_6⟩
 | 5 => ⟨R7.Core.Certificates.Terminal108.polynomial_7, 5370955706329282552321333676188672432925429262210397983558468672360534877519068701805642904246991603143463078854656000000000, by norm_num, R7.Core.Certificates.Terminal108.positive_7⟩
 | 6 => ⟨R7.Core.Certificates.Terminal108.polynomial_8, 42580000633684238924956561352572562245421759151361955947083478780591981792442791867432600695721311065831895992163315339108272622796800000000000, by norm_num, R7.Core.Certificates.Terminal108.positive_8⟩
theorem bound_230 : minorBindings polynomial_230 witness_230 := by
 decide +kernel
theorem positive_230 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_230 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_230 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL038
