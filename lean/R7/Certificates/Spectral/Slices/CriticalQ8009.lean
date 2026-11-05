import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal116
import R7.Certificates.Spectral.Terminal.Terminal117

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8009
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_54 : BiPoly := [[61619220582],[130266845250],[1125551932260],[598092898500],[3866043093264],[734901570000],[3868123494312],[0],[77789294352]]
def witness_54 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal116.polynomial_23, 123238441164, by norm_num, R7.Core.Certificates.Terminal116.positive_23⟩
 | 1 => ⟨R7.Core.Certificates.Terminal116.polynomial_24, 260453080190313599538780, by norm_num, R7.Core.Certificates.Terminal116.positive_24⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_25, 1969761410395691812882907064030555840, by norm_num, R7.Core.Certificates.Terminal116.positive_25⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_26, 15097895197215355310721360832514756546298876764160, by norm_num, R7.Core.Certificates.Terminal116.positive_26⟩
 | 4 => ⟨R7.Core.Certificates.Terminal116.polynomial_27, 2348909227183664729999940718508988338727324481548431048048640, by norm_num, R7.Core.Certificates.Terminal116.positive_27⟩
theorem bound_54 : ordinaryBindings polynomial_54 witness_54 := by
 decide +kernel
theorem positive_54 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_54 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_54 ρ hρ u
def polynomial_55 : BiPoly := [[410024560845],[539726831250],[6263843392320],[2420853795000],[20577276556416],[2752161750000],[19591794321840],[0],[388946471760]]
def witness_55 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal116.polynomial_28, 820049121690, by norm_num, R7.Core.Certificates.Terminal116.positive_28⟩
 | 1 => ⟨R7.Core.Certificates.Terminal116.polynomial_29, 9982013492180286206279100, by norm_num, R7.Core.Certificates.Terminal116.positive_29⟩
 | 2 => ⟨R7.Core.Certificates.Terminal116.polynomial_30, 405999379418301166846026364546933411200, by norm_num, R7.Core.Certificates.Terminal116.positive_30⟩
 | 3 => ⟨R7.Core.Certificates.Terminal116.polynomial_31, 15832904966636716006082134466239012593721733721216000, by norm_num, R7.Core.Certificates.Terminal116.positive_31⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_0, 12316305048969462408477529802827109570388549316194357313720320000, by norm_num, R7.Core.Certificates.Terminal117.positive_0⟩
theorem bound_55 : ordinaryBindings polynomial_55 witness_55 := by
 decide +kernel
theorem positive_55 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_55 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_55 ρ hρ u
def polynomial_56 : BiPoly := [[1233191882880],[993116021250],[16079064342060],[3986129430000],[48114019977120],[3838149900000],[41695357146480],[0],[777892943520]]
def witness_56 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_1, 2466383765760, by norm_num, R7.Core.Certificates.Terminal117.positive_1⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_2, 78328007092071128660168700, by norm_num, R7.Core.Certificates.Terminal117.positive_2⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_3, 7498161662414751513097811759434680288000, by norm_num, R7.Core.Certificates.Terminal117.positive_3⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_4, 624123176127851776570850149561425395451342569172480000, by norm_num, R7.Core.Certificates.Terminal117.positive_4⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_5, 971002029194292028661919989342338875829049780138919355556659200000, by norm_num, R7.Core.Certificates.Terminal117.positive_5⟩
theorem bound_56 : ordinaryBindings polynomial_56 witness_56 := by
 decide +kernel
theorem positive_56 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_56 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_56 ρ hρ u
def polynomial_57 : BiPoly := [[2064906334710],[1032484916250],[22697550849570],[3445906882500],[60347713162176],[2707532100000],[46216540451520],[0],[777892943520]]
def witness_57 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_6, 4129812669420, by norm_num, R7.Core.Certificates.Terminal117.positive_6⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_7, 186407241024433971604236300, by norm_num, R7.Core.Certificates.Terminal117.positive_7⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_8, 22449462897181961658420011469661177377600, by norm_num, R7.Core.Certificates.Terminal117.positive_8⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_9, 2073706519037499768733738910645833722424837627067904000, by norm_num, R7.Core.Certificates.Terminal117.positive_9⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_10, 3226243336181387224723214848674891717123071147355807738953564160000, by norm_num, R7.Core.Certificates.Terminal117.positive_10⟩
theorem bound_57 : ordinaryBindings polynomial_57 witness_57 := by
 decide +kernel
theorem positive_57 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_57 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_57 ρ hρ u
def polynomial_58 : BiPoly := [[1864167619185],[613562021250],[17324330894910],[1846594642500],[39871511576784],[1234753650000],[26373569279400],[0],[388946471760]]
def witness_58 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_11, 3728335238370, by norm_num, R7.Core.Certificates.Terminal117.positive_11⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_12, 128805368359429675087830900, by norm_num, R7.Core.Certificates.Terminal117.positive_12⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_13, 10258616177164201021321000871022903151200, by norm_num, R7.Core.Certificates.Terminal117.positive_13⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_14, 540916270118724450373187236015128833969914296490560000, by norm_num, R7.Core.Certificates.Terminal117.positive_14⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_15, 420774949560513982568592781507901523908881999219171724293171200000, by norm_num, R7.Core.Certificates.Terminal117.positive_15⟩
theorem bound_58 : ordinaryBindings polynomial_58 witness_58 := by
 decide +kernel
theorem positive_58 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_58 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_58 ρ hρ u
def polynomial_59 : BiPoly := [[170651006260],[142706478750],[2299975707780],[617081032500],[7274779215504],[609938550000],[6614323724040],[0],[129648823920]]
def witness_59 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_16, 341302012520, by norm_num, R7.Core.Certificates.Terminal117.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_17, 1549607536547626641248700, by norm_num, R7.Core.Certificates.Terminal117.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_18, 22416141345855475955578127941669689600, by norm_num, R7.Core.Certificates.Terminal117.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_19, 295958738212978177357289093811336963229575715968000, by norm_num, R7.Core.Certificates.Terminal117.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_20, 76741404676319566349995409304164775291077553071686328709120000, by norm_num, R7.Core.Certificates.Terminal117.positive_20⟩
theorem bound_59 : ordinaryBindings polynomial_59 witness_59 := by
 decide +kernel
theorem positive_59 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_59 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_59 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8009
