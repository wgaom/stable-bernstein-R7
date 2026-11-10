import R7.Spectral.SliceInteger
import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch14
import R7.Certificates.Spectral.Terminal.Batches.Batch15
import R7.Certificates.Spectral.Terminal.Batches.Batch00
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.CriticalQ8009
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_54 : BiPoly := r7_rat_grid%[[61619220582],[130266845250],[1125551932260],[598092898500],[3866043093264],[734901570000],[3868123494312],[0],[77789294352]]
noncomputable def witness_54 : Fin 5 → MinorWitness
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
noncomputable def polynomial_55 : BiPoly := r7_rat_grid%[[410024560845],[539726831250],[6263843392320],[2420853795000],[20577276556416],[2752161750000],[19591794321840],[0],[388946471760]]
noncomputable def witness_55 : Fin 5 → MinorWitness
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
noncomputable def polynomial_56 : BiPoly := r7_rat_grid%[[1233191882880],[993116021250],[16079064342060],[3986129430000],[48114019977120],[3838149900000],[41695357146480],[0],[777892943520]]
noncomputable def witness_56 : Fin 5 → MinorWitness
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
noncomputable def polynomial_57 : BiPoly := r7_rat_grid%[[2064906334710],[1032484916250],[22697550849570],[3445906882500],[60347713162176],[2707532100000],[46216540451520],[0],[777892943520]]
noncomputable def witness_57 : Fin 5 → MinorWitness
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
noncomputable def polynomial_58 : BiPoly := r7_rat_grid%[[1864167619185],[613562021250],[17324330894910],[1846594642500],[39871511576784],[1234753650000],[26373569279400],[0],[388946471760]]
noncomputable def witness_58 : Fin 5 → MinorWitness
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
noncomputable def polynomial_59 : BiPoly := r7_rat_grid%[[170651006260],[142706478750],[2299975707780],[617081032500],[7274779215504],[609938550000],[6614323724040],[0],[129648823920]]
noncomputable def witness_59 : Fin 5 → MinorWitness
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

namespace R7.Core.SpectralSliceCertificates.CriticalQ8010
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_60 : BiPoly := r7_rat_grid%[[863722709180],[373412445000],[10974404978040],[1478890455000],[32476638028512],[1249630200000],[27796904764320],[0],[518595295680]]
noncomputable def witness_60 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_21, 1727445418360, by norm_num, R7.Core.Certificates.Terminal117.positive_21⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_22, 37775934343003870800628800, by norm_num, R7.Core.Certificates.Terminal117.positive_22⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_23, 2449892566490270334357129848504856691200, by norm_num, R7.Core.Certificates.Terminal117.positive_23⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_24, 136139870728365516150673657761974239893800222035968000, by norm_num, R7.Core.Certificates.Terminal117.positive_24⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_25, 141202993028427383622548841956516315996537155891184953110036480000, by norm_num, R7.Core.Certificates.Terminal117.positive_25⟩
theorem bound_60 : ordinaryBindings polynomial_60 witness_60 := by
 decide +kernel
theorem positive_60 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_60 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_60 ρ hρ u
noncomputable def polynomial_61 : BiPoly := r7_rat_grid%[[2043024692040],[313331261250],[22245477842700],[859732335000],[59297148319392],[535555800000],[45714186750960],[0],[777892943520]]
noncomputable def witness_61 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_26, 4086049384080, by norm_num, R7.Core.Certificates.Terminal117.positive_26⟩
 | 1 => ⟨R7.Core.Certificates.Terminal117.polynomial_27, 181694065596182728496869500, by norm_num, R7.Core.Certificates.Terminal117.positive_27⟩
 | 2 => ⟨R7.Core.Certificates.Terminal117.polynomial_28, 21544859751554106655155619952938286688000, by norm_num, R7.Core.Certificates.Terminal117.positive_28⟩
 | 3 => ⟨R7.Core.Certificates.Terminal117.polynomial_29, 1969759370916968182434762279762182835220203478440960000, by norm_num, R7.Core.Certificates.Terminal117.positive_29⟩
 | 4 => ⟨R7.Core.Certificates.Terminal117.polynomial_30, 3064523830137407721896723180351340262539726422435562469869158400000, by norm_num, R7.Core.Certificates.Terminal117.positive_30⟩
theorem bound_61 : ordinaryBindings polynomial_61 witness_61 := by
 decide +kernel
theorem positive_61 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_61 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_61 ρ hρ u
noncomputable def polynomial_62 : BiPoly := r7_rat_grid%[[2358603965720],[0],[22081875116100],[0],[51342008264160],[0],[34494954105120],[0],[518595295680]]
noncomputable def witness_62 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal117.polynomial_31, 4717207931440, by norm_num, R7.Core.Certificates.Terminal117.positive_31⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_0, 208329592877468981680368000, by norm_num, R7.Core.Certificates.Terminal118.positive_0⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_1, 21392119358368201463395026999260021760000, by norm_num, R7.Core.Certificates.Terminal118.positive_1⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_2, 1475840350956320422988418956000635445624825054822400000, by norm_num, R7.Core.Certificates.Terminal118.positive_2⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_3, 1530727726361335921049003595405732898383389423307789475774464000000, by norm_num, R7.Core.Certificates.Terminal118.positive_3⟩
theorem bound_62 : ordinaryBindings polynomial_62 witness_62 := by
 decide +kernel
theorem positive_62 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_62 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_62 ρ hρ u
noncomputable def polynomial_63 : BiPoly := r7_rat_grid%[[261210348330],[43999743750],[3187226781240],[122364195000],[8963539798752],[14876550000],[7284128658120],[0],[129648823920]]
noncomputable def witness_63 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_4, 522420696660, by norm_num, R7.Core.Certificates.Terminal118.positive_4⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_5, 3328210493487554773254300, by norm_num, R7.Core.Certificates.Terminal118.positive_5⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_6, 59657272230884168564293846331737267200, by norm_num, R7.Core.Certificates.Terminal118.positive_6⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_7, 869101756072444599681871144473536639290113779328000, by norm_num, R7.Core.Certificates.Terminal118.positive_7⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_8, 225356041083198321336219600051956865693985030345723215851520000, by norm_num, R7.Core.Certificates.Terminal118.positive_8⟩
theorem bound_63 : ordinaryBindings polynomial_63 witness_63 := by
 decide +kernel
theorem positive_63 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_63 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_63 ρ hρ u
noncomputable def polynomial_64 : BiPoly := r7_rat_grid%[[1143809903055],[-172659491250],[12063811568190],[-816303712500],[31476805683408],[-773580600000],[23610623926320],[0],[388946471760]]
noncomputable def witness_64 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_9, 2287619806110, by norm_num, R7.Core.Certificates.Terminal118.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_10, 55165017261222056860719300, by norm_num, R7.Core.Certificates.Terminal118.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_11, 3471312698243151605901337671034223248800, by norm_num, R7.Core.Certificates.Terminal118.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_12, 163886705065022631994141929974172003623599364456832000, by norm_num, R7.Core.Certificates.Terminal118.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_13, 127486311406824548197340793304262377473537815754526310454128640000, by norm_num, R7.Core.Certificates.Terminal118.positive_13⟩
theorem bound_64 : ordinaryBindings polynomial_64 witness_64 := by
 decide +kernel
theorem positive_64 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_64 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_64 ρ hρ u
noncomputable def polynomial_65 : BiPoly := r7_rat_grid%[[300797752224],[-95463642750],[2913188558532],[-399940002000],[7212598394112],[-318358170000],[5073772375656],[0],[77789294352]]
noncomputable def witness_65 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal118.polynomial_14, 601595504448, by norm_num, R7.Core.Certificates.Terminal118.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal118.polynomial_15, 3496008973757301401138172, by norm_num, R7.Core.Certificates.Terminal118.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal118.polynomial_16, 50334391012590487734752979294654486528, by norm_num, R7.Core.Certificates.Terminal118.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal118.polynomial_17, 510416158093068438919705304063802546628728014324736, by norm_num, R7.Core.Certificates.Terminal118.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal118.polynomial_18, 79409825527837335612012177581829596176218657531310722437382144, by norm_num, R7.Core.Certificates.Terminal118.positive_18⟩
theorem bound_65 : ordinaryBindings polynomial_65 witness_65 := by
 decide +kernel
theorem positive_65 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_65 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_65 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8010

namespace R7.Core.SpectralSliceCertificates.CriticalQ8011
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_66 : BiPoly := r7_rat_grid%[[10269870097],[21032235750],[155314182411],[111095023500],[577206291624],[154716120000],[636314687376],[0],[12964882392]]
noncomputable def witness_66 : Fin 5 → MinorWitness
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
noncomputable def polynomial_67 : BiPoly := r7_rat_grid%[[51058838514],[100132333500],[890623437660],[538109361000],[3314452140576],[770605290000],[3667182014088],[0],[77789294352]]
noncomputable def witness_67 : Fin 5 → MinorWitness
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
noncomputable def polynomial_68 : BiPoly := r7_rat_grid%[[167212108245],[210252296250],[2562540984120],[1108098405000],[8970081698016],[1487655000000],[9293543460360],[0],[194473235880]]
noncomputable def witness_68 : Fin 5 → MinorWitness
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
noncomputable def polynomial_69 : BiPoly := r7_rat_grid%[[332572456870],[258732412500],[4440282758820],[1271774565000],[14190055481376],[1457901900000],[13228647448080],[0],[259297647840]]
noncomputable def witness_69 : Fin 5 → MinorWitness
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
noncomputable def polynomial_70 : BiPoly := r7_rat_grid%[[416951021955],[200523258750],[4740298614105],[881401522500],[13505730499656],[833086800000],[11051781412320],[0],[194473235880]]
noncomputable def witness_70 : Fin 5 → MinorWitness
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
noncomputable def polynomial_71 : BiPoly := r7_rat_grid%[[40498456446],[74071252500],[849361780854],[409648581000],[3165666531408],[612913860000],[3516475903920],[0],[77789294352]]
noncomputable def witness_71 : Fin 5 → MinorWitness
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

namespace R7.Core.SpectralSliceCertificates.CriticalQ8012
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_72 : BiPoly := r7_rat_grid%[[258823872135],[290269248750],[4528969720860],[1576744740000],[16430905197504],[2246359050000],[17582379519600],[0],[388946471760]]
noncomputable def witness_72 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_17, 517647744270, by norm_num, R7.Core.Certificates.Terminal119.positive_17⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_18, 4604565682970731752381900, by norm_num, R7.Core.Certificates.Terminal119.positive_18⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_19, 150027427957449477465680188631869555200, by norm_num, R7.Core.Certificates.Terminal119.positive_19⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_20, 5252443121054511526505181120929416537349733363840000, by norm_num, R7.Core.Certificates.Terminal119.positive_20⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_21, 4085838440108469657728883840690516908395150106084648730316800000, by norm_num, R7.Core.Certificates.Terminal119.positive_21⟩
theorem bound_72 : ordinaryBindings polynomial_72 witness_72 := by
 decide +kernel
theorem positive_72 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_72 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_72 ρ hρ u
noncomputable def polynomial_73 : BiPoly := r7_rat_grid%[[762242858340],[468115571250],[11368143011250],[2376308182500],[37940428672992],[2945556900000],[37174173841440],[0],[777892943520]]
noncomputable def witness_73 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_22, 1524485716680, by norm_num, R7.Core.Certificates.Terminal119.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_23, 34442011103605665278737500, by norm_num, R7.Core.Certificates.Terminal119.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_24, 2604880803455638425660901587062965200000, by norm_num, R7.Core.Certificates.Terminal119.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_25, 193369754239093251916796424861877403744707075776000000, by norm_num, R7.Core.Certificates.Terminal119.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_26, 300841934625574495178651306128836646064691315591128656343040000000, by norm_num, R7.Core.Certificates.Terminal119.positive_26⟩
theorem bound_73 : ordinaryBindings polynomial_73 witness_73 := by
 decide +kernel
theorem positive_73 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_73 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_73 ρ hρ u
noncomputable def polynomial_74 : BiPoly := r7_rat_grid%[[1270701840930],[398649288750],[15860577720990],[1760664172500],[47431774572480],[1844692200000],[41193003445920],[0],[777892943520]]
noncomputable def witness_74 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal119.polynomial_27, 2541403681860, by norm_num, R7.Core.Certificates.Terminal119.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal119.polynomial_28, 80457339977680466731920300, by norm_num, R7.Core.Certificates.Terminal119.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal119.polynomial_29, 7624590630364301497869329343457241688000, by norm_num, R7.Core.Certificates.Terminal119.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal119.polynomial_30, 627885788798310427978827914410747546684872555025920000, by norm_num, R7.Core.Certificates.Terminal119.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal119.polynomial_31, 976855848885389484846322821161038070828628259370352157392076800000, by norm_num, R7.Core.Certificates.Terminal119.positive_31⟩
theorem bound_74 : ordinaryBindings polynomial_74 witness_74 := by
 decide +kernel
theorem positive_74 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_74 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_74 ρ hρ u
noncomputable def polynomial_75 : BiPoly := r7_rat_grid%[[157577731020],[105091117500],[2405565268725],[552623287500],[8516738868984],[714074400000],[8791189759800],[0],[194473235880]]
noncomputable def witness_75 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_0, 315155462040, by norm_num, R7.Core.Certificates.Terminal120.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_1, 1505209924487409467148000, by norm_num, R7.Core.Certificates.Terminal120.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_2, 25542713625949559334115205004525264000, by norm_num, R7.Core.Certificates.Terminal120.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_3, 448334175006588475633725885284054473794383174400000, by norm_num, R7.Core.Certificates.Terminal120.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_4, 174377995538242962352014413144215492969968715388388754944000000, by norm_num, R7.Core.Certificates.Terminal120.positive_4⟩
theorem bound_75 : ordinaryBindings polynomial_75 witness_75 := by
 decide +kernel
theorem positive_75 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_75 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_75 ρ hρ u
noncomputable def polynomial_76 : BiPoly := r7_rat_grid%[[751955259060],[212579463750],[11191111030230],[1107385447500],[37453791311136],[1249630200000],[36671820140880],[0],[777892943520]]
noncomputable def witness_76 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_5, 1503910518120, by norm_num, R7.Core.Certificates.Terminal120.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_6, 33615669147215055001472700, by norm_num, R7.Core.Certificates.Terminal120.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_7, 2516224264775707747378572408619569974400, by norm_num, R7.Core.Certificates.Terminal120.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_8, 184496553933992130357180202030710754280544851986944000, by norm_num, R7.Core.Certificates.Terminal120.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_9, 287037134818019148136124912649475740170024949563013177538805760000, by norm_num, R7.Core.Certificates.Terminal120.positive_9⟩
theorem bound_76 : ordinaryBindings polynomial_76 witness_76 := by
 decide +kernel
theorem positive_76 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_76 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_76 ρ hρ u
noncomputable def polynomial_77 : BiPoly := r7_rat_grid%[[1773467605080],[0],[22458732815700],[0],[68121715357872],[0],[60282444067200],[0],[1166839415280]]
noncomputable def witness_77 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_10, 3546935210160, by norm_num, R7.Core.Certificates.Terminal120.positive_10⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_11, 159319340399164336095024000, by norm_num, R7.Core.Certificates.Terminal120.positive_11⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_12, 21706213515351580257918354266316857856000, by norm_num, R7.Core.Certificates.Terminal120.positive_12⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_13, 2617007204299764650882189881927040953313545823846400000, by norm_num, R7.Core.Certificates.Terminal120.positive_13⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_14, 6107254312097369774153975555987361411169983175200838513065984000000, by norm_num, R7.Core.Certificates.Terminal120.positive_14⟩
theorem bound_77 : ordinaryBindings polynomial_77 witness_77 := by
 decide +kernel
theorem positive_77 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_77 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_77 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8012

namespace R7.Core.SpectralSliceCertificates.CriticalQ8013
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_78 : BiPoly := r7_rat_grid%[[291199864680],[1598152500],[4253320328520],[1425915000],[13613542382112],[-119012400000],[12726293747520],[0],[259297647840]]
noncomputable def witness_78 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_15, 582399729360, by norm_num, R7.Core.Certificates.Terminal120.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_16, 4954262662331455322444400, by norm_num, R7.Core.Certificates.Terminal120.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_17, 134890128267373907838532923043349145600, by norm_num, R7.Core.Certificates.Terminal120.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_18, 3433232620007159736032648345195794792195228237824000, by norm_num, R7.Core.Certificates.Terminal120.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_19, 1780458285710834087024842018710275907751088544279422639800320000, by norm_num, R7.Core.Certificates.Terminal120.positive_19⟩
theorem bound_78 : ordinaryBindings polynomial_78 witness_78 := by
 decide +kernel
theorem positive_78 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_78 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_78 ρ hρ u
noncomputable def polynomial_79 : BiPoly := r7_rat_grid%[[9979358126],[16003390500],[269366708016],[93729267000],[1005626974080],[151740810000],[1121923264584],[0],[25929764784]]
noncomputable def witness_79 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_20, 19958716252, by norm_num, R7.Core.Certificates.Terminal120.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_21, 10496318878557865502064, by norm_num, R7.Core.Certificates.Terminal120.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_22, 20935421960769867032293519801002240, by norm_num, R7.Core.Certificates.Terminal120.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_23, 46734193291264397516974121424804650881393336320, by norm_num, R7.Core.Certificates.Terminal120.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_24, 2423613278824953259137225231920479081007534985925208309760, by norm_num, R7.Core.Certificates.Terminal120.positive_24⟩
theorem bound_79 : ordinaryBindings polynomial_79 witness_79 := by
 decide +kernel
theorem positive_79 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_79 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_79 ρ hρ u
noncomputable def polynomial_80 : BiPoly := r7_rat_grid%[[61074509260],[53344635000],[1310952491160],[312430890000],[4973882332992],[505802700000],[5525890706160],[0],[129648823920]]
noncomputable def witness_80 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_25, 122149018520, by norm_num, R7.Core.Certificates.Terminal120.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_26, 317417470159802727566400, by norm_num, R7.Core.Certificates.Terminal120.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal120.polynomial_27, 3145670954422634038264923553181337600, by norm_num, R7.Core.Certificates.Terminal120.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal120.polynomial_28, 34684060849601408477884930476655668833994719232000, by norm_num, R7.Core.Certificates.Terminal120.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal120.polynomial_29, 8993495395841077219866597130778744958256826127838811258880000, by norm_num, R7.Core.Certificates.Terminal120.positive_29⟩
theorem bound_80 : ordinaryBindings polynomial_80 witness_80 := by
 decide +kernel
theorem positive_80 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_80 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_80 ρ hρ u
noncomputable def polynomial_81 : BiPoly := r7_rat_grid%[[175589448690],[53344635000],[3138479248680],[312430890000],[11103563633952],[505802700000],[11554135112880],[0],[259297647840]]
noncomputable def witness_81 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal120.polynomial_30, 351178897380, by norm_num, R7.Core.Certificates.Terminal120.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal120.polynomial_31, 2201489713919623215916800, by norm_num, R7.Core.Certificates.Terminal120.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_0, 48854482608853576072957470372574387200, by norm_num, R7.Core.Certificates.Terminal121.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_1, 1128379364725157269976508001085057836342537654272000, by norm_num, R7.Core.Certificates.Terminal121.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_2, 585172230288853496357968753476591329467959364578721455144960000, by norm_num, R7.Core.Certificates.Terminal121.positive_2⟩
theorem bound_81 : ordinaryBindings polynomial_81 witness_81 := by
 decide +kernel
theorem positive_81 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_81 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_81 ρ hρ u
noncomputable def polynomial_82 : BiPoly := r7_rat_grid%[[72252227890],[26672317500],[1275071442240],[156215445000],[4919629795584],[252901350000],[5442165089400],[0],[129648823920]]
noncomputable def witness_82 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal121.polynomial_3, 144504455780, by norm_num, R7.Core.Certificates.Terminal121.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal121.polynomial_4, 367795597162201002044400, by norm_num, R7.Core.Certificates.Terminal121.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_5, 3615309976402395797924364241683859200, by norm_num, R7.Core.Certificates.Terminal121.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_6, 39326703609131279630037759204855327700410024960000, by norm_num, R7.Core.Certificates.Terminal121.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_7, 10197321743148579553838096372203295180208715675683690086400000, by norm_num, R7.Core.Certificates.Terminal121.positive_7⟩
theorem bound_82 : ordinaryBindings polynomial_82 witness_82 := by
 decide +kernel
theorem positive_82 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_82 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_82 ρ hρ u
noncomputable def polynomial_83 : BiPoly := r7_rat_grid%[[320093904470],[0],[5688622133160],[0],[20942823225120],[0],[22438465291680],[0],[518595295680]]
noncomputable def witness_83 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal121.polynomial_8, 640187808940, by norm_num, R7.Core.Certificates.Terminal121.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal121.polynomial_9, 7283573078630578636900800, by norm_num, R7.Core.Certificates.Terminal121.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_10, 305077166866006524483021171395016192000, by norm_num, R7.Core.Certificates.Terminal121.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_11, 13690926840013910241721393419627374542247205765120000, by norm_num, R7.Core.Certificates.Terminal121.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_12, 14200100505460523674236972585266529232317588650832414061363200000, by norm_num, R7.Core.Certificates.Terminal121.positive_12⟩
theorem bound_83 : ordinaryBindings polynomial_83 witness_83 := by
 decide +kernel
theorem positive_83 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_83 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_83 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8013

namespace R7.Core.SpectralSliceCertificates.CriticalQ8014
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_84 : BiPoly := r7_rat_grid%[[20857486630],[0],[309797598330],[0],[1216344314544],[0],[1339609868160],[0],[32412205980]]
noncomputable def witness_84 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal121.polynomial_13, 41714973260, by norm_num, R7.Core.Certificates.Terminal121.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal121.polynomial_14, 25846397060696341311600, by norm_num, R7.Core.Certificates.Terminal121.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal121.polynomial_15, 62876236232449495271973543831820800, by norm_num, R7.Core.Certificates.Terminal121.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal121.polynomial_16, 168459253059497366950294044791106886201491456000, by norm_num, R7.Core.Certificates.Terminal121.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal121.polynomial_17, 10920272018802747705721150002673404935518321710164213760000, by norm_num, R7.Core.Certificates.Terminal121.positive_17⟩
theorem bound_84 : ordinaryBindings polynomial_84 witness_84 := by
 decide +kernel
theorem positive_84 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_84 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_84 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8014

namespace R7.Core.SpectralSliceCertificates.Entry000
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_0 : BiPoly := r7_rat_grid%[[105759354829824,-708981990042240,2860714298924160],[0,1444308557961600,28036958209920000],[837982036296576,23520976850612640,100380901894701840],[0,43801073573313600,139183004265840000],[2715487046717760,244900443711132000,445269755583473400],[0,66614708353629600,250905825641160000],[4577082914646720,576406904489735400,756691126293124800],[0,-1383169684496400,187088766180480000],[4188590702840160,506060044538049000,542529634740854400],[0,-11441037087158400,43900580037600000],[1936777876021656,163299623934533040,128708744989469040],[0,0,0],[340100332584804,-1432692003894840,1708002866952360]]
noncomputable def witness_0 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_0, 883200, by norm_num, R7.Core.Certificates.Terminal000.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_1, 84787200, by norm_num, R7.Core.Certificates.Terminal000.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_2, 221184, by norm_num, R7.Core.Certificates.Terminal000.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_3, 7962624000, by norm_num, R7.Core.Certificates.Terminal000.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_4, 1146617856000000, by norm_num, R7.Core.Certificates.Terminal000.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_5, 24766945689600000000, by norm_num, R7.Core.Certificates.Terminal000.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_6, 166106951351009280000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_6⟩
theorem bound_0 : minorBindings polynomial_0 witness_0 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_0 witness_0 (by decide +kernel)
theorem positive_0 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_0 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_0 ρ hρ u
noncomputable def polynomial_1 : BiPoly := r7_rat_grid%[[951834193468416,-6380837910380160,25746428690317440],[0,13359854161144800,259341863441760000],[7960829344817472,223449280080820080,953618567999667480],[0,427060467339807600,1357034291591940000],[27154870467177600,2449004437111320000,4452697555834734000],[0,682800760624703400,2571784712821890000],[48059370603790560,6052272497142221700,7945256826077810400],[0,-14869074108336300,2011204236440160000],[46074497731241760,5566660489918539000,5967825982149398400],[0,-128711667230532000,493881525423000000],[22272945574249044,1877945675247129960,1480150567378893960],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
noncomputable def witness_1 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_8, 7948800, by norm_num, R7.Core.Certificates.Terminal000.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_9, 190771200, by norm_num, R7.Core.Certificates.Terminal000.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_10, 27648, by norm_num, R7.Core.Certificates.Terminal000.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_11, 1492992000, by norm_num, R7.Core.Certificates.Terminal000.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_12, 6718464000000, by norm_num, R7.Core.Certificates.Terminal000.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_13, 72559411200000000, by norm_num, R7.Core.Certificates.Terminal000.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_14, 5839697508433920000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_14⟩
theorem bound_1 : minorBindings polynomial_1 witness_1 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_1 witness_1 (by decide +kernel)
theorem positive_1 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_1 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_1 ρ hρ u
noncomputable def polynomial_2 : BiPoly := r7_rat_grid%[[4521212418974976,-14401445984570760,166199154083007840],[0,87794615861887200,1187539446266640000],[38547173669642496,1220300387133991440,4868577420010784640],[0,2032980975433479600,6351020288593740000],[134416608812529120,12397805704645287750,22544357777446308300],[0,3267869281125350400,12332238594863715000],[243729665204937840,30895204123667751300,40698061011755333100],[0,-78327488528528400,9902724216786630000],[239796817737599160,29041316581253071500,31158375130989914400],[0,-652139113968028800,2502333062143200000],[119111839375331844,10042926871973781960,7915587816852345960],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
noncomputable def witness_2 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_16, 55200, by norm_num, R7.Core.Certificates.Terminal000.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_17, 15897600, by norm_num, R7.Core.Certificates.Terminal000.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_18, 442368, by norm_num, R7.Core.Certificates.Terminal000.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_19, 23887872000, by norm_num, R7.Core.Certificates.Terminal000.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_20, 429981696000000, by norm_num, R7.Core.Certificates.Terminal000.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_21, 13931406950400000000, by norm_num, R7.Core.Certificates.Terminal000.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_22, 6166720568906219520000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_22⟩
theorem bound_2 : minorBindings polynomial_2 witness_2 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_2 witness_2 (by decide +kernel)
theorem positive_2 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_2 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_2 ρ hρ u
noncomputable def polynomial_3 : BiPoly := r7_rat_grid%[[14277512902026240,17836086054365100,741973101721761600],[0,394871340019647000,3548357969621400000],[122554872808374240,4598490215418671100,16826127480517769100],[0,6230524454179236900,18965691381383235000],[430404696904764960,41302289484838877625,75114877892493033900],[0,9690643523406645000,36858118518032625000],[786686125954905000,100989888576508732500,133898457051229950000],[0,-275830012429587000,29697873907219650000],[781172166079689840,95073988620843801000,102167312299929345600],[0,-1970718638263034400,7561874911476600000],[392197519894385340,33068173846742940600,26063520860367480600],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
noncomputable def witness_3 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal000.polynomial_24, 414000, by norm_num, R7.Core.Certificates.Terminal000.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal000.polynomial_25, 16560000, by norm_num, R7.Core.Certificates.Terminal000.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal000.polynomial_26, 432000, by norm_num, R7.Core.Certificates.Terminal000.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal000.polynomial_27, 972000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal000.polynomial_28, 17496000000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal000.polynomial_29, 76527504000000000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal000.polynomial_30, 112916026041984000000000000000000, by norm_num, R7.Core.Certificates.Terminal000.positive_30⟩
theorem bound_3 : minorBindings polynomial_3 witness_3 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_3 witness_3 (by decide +kernel)
theorem positive_3 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_3 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_3 ρ hρ u
noncomputable def polynomial_4 : BiPoly := r7_rat_grid%[[33016748585935680,217179004622731950,2352740551072261200],[0,1164861934360749000,7650569737851300000],[282033329091066360,12693005198445369150,42723202207586634900],[0,13468824530444068200,40204163909838330000],[985891515898966740,99517262750633341125,180987638173833756600],[0,19760275636761762000,76703033950208325000],[1793644367177183400,234291418281003190500,313320486980067156000],[0,-724732400026656000,60664174205141700000],[1772821014977097720,217311970265968720500,234060577297486624800],[0,-3964319350700385600,15211550983028400000],[886075878279907620,74709577950048865800,58884250832682085800],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
noncomputable def witness_4 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal001.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_1, 12420000, by norm_num, R7.Core.Certificates.Terminal001.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_2, 486000, by norm_num, R7.Core.Certificates.Terminal001.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_3, 131220000000, by norm_num, R7.Core.Certificates.Terminal001.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_4, 2361960000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_5, 8800662960000000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_6, 29217021738363360000000000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_6⟩
theorem bound_4 : minorBindings polynomial_4 witness_4 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_4 witness_4 (by decide +kernel)
theorem positive_4 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_4 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_4 ρ hρ u
noncomputable def polynomial_5 : BiPoly := r7_rat_grid%[[58359333987032256,758867818044112065,5449337030903963040],[0,2335848979481579400,12516968373861780000],[491869268367455844,26421790298720688660,82564528689499215960],[0,21264731638104928500,63696262796392275000],[1694463917151882240,180923431143842168625,328962207011702714100],[0,28951581662012611800,117231486258852405000],[3034605972410775360,404519586276043982700,546216346135936742400],[0,-1457336480226190200,89180832551489640000],[2948767854799472640,364591755128758446000,393767287906681497600],[0,-5611828691251195200,21533234508442800000],[1446773073388177032,121984819079096180880,96145432507133372880],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
noncomputable def witness_5 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_8, 20700, by norm_num, R7.Core.Certificates.Terminal001.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_9, 165600, by norm_num, R7.Core.Certificates.Terminal001.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_10, 3456, by norm_num, R7.Core.Certificates.Terminal001.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_11, 186624000, by norm_num, R7.Core.Certificates.Terminal001.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_12, 3359232000000, by norm_num, R7.Core.Certificates.Terminal001.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_13, 653034700800000000, by norm_num, R7.Core.Certificates.Terminal001.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_14, 3468780320009748480000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_14⟩
theorem bound_5 : minorBindings polynomial_5 witness_5 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_5 witness_5 (by decide +kernel)
theorem positive_5 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_5 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_5 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry000

namespace R7.Core.SpectralSliceCertificates.Entry001
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_6 : BiPoly := r7_rat_grid%[[80623330668629424,1671090749470944885,9451788755851388160],[0,3266670776965111200,15917511072475440000],[664388820090013428,42052531127402339670,123230835741782738520],[0,24746632070979985200,77377925899136880000],[2234166967687037040,252608005877816273625,459085695088555083600],[0,30920245884833911200,135135773035903395000],[3897386101821682080,530761487356404953100,723701111423766892200],[0,-2221260063508004400,97024610082308580000],[3679676932445080560,459143345731126959000,497308527955800590400],[0,-5766282691927833600,22125892338950400000],[1748910422047555368,147459560412883335120,116223996725490543120],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
noncomputable def witness_6 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_16, 6900, by norm_num, R7.Core.Certificates.Terminal001.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_17, 82800, by norm_num, R7.Core.Certificates.Terminal001.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_18, 432, by norm_num, R7.Core.Certificates.Terminal001.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_19, 7776000, by norm_num, R7.Core.Certificates.Terminal001.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_20, 1959552000000, by norm_num, R7.Core.Certificates.Terminal001.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_21, 888852787200000000, by norm_num, R7.Core.Certificates.Terminal001.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_22, 5508294674830295040000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_22⟩
theorem bound_6 : minorBindings polynomial_6 witness_6 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_6 witness_6 (by decide +kernel)
theorem positive_6 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_6 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_6 ρ hρ u
noncomputable def polynomial_7 : BiPoly := r7_rat_grid%[[87539000980548384,2609812347148543410,12417718965374194560],[0,3193892914627135800,15878312121765960000],[699269822350858404,51277440128968947060,142254154881857983860],[0,21054427362804795300,72752032318561695000],[2272862658102765120,271412558348957575875,492935942597908173300],[0,23967183275563624200,118728303034458195000],[3820719963001349520,531206889278021793900,730907175455267176800],[0,-2518412392921741200,79096268300645340000],[3463964511248812320,435995172758307618000,473507500533838588800],[0,-4376196685838088000,16791971864382000000],[1574600413205606328,132762594258775361520,104640209676438329520],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
noncomputable def witness_7 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal001.polynomial_24, 41400, by norm_num, R7.Core.Certificates.Terminal001.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal001.polynomial_25, 2980800, by norm_num, R7.Core.Certificates.Terminal001.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal001.polynomial_26, 279936, by norm_num, R7.Core.Certificates.Terminal001.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal001.polynomial_27, 15116544000, by norm_num, R7.Core.Certificates.Terminal001.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal001.polynomial_28, 2176782336000000, by norm_num, R7.Core.Certificates.Terminal001.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal001.polynomial_29, 141055495372800000000, by norm_num, R7.Core.Certificates.Terminal001.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal001.polynomial_30, 749256549122105671680000000000, by norm_num, R7.Core.Certificates.Terminal001.positive_30⟩
theorem bound_7 : minorBindings polynomial_7 witness_7 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_7 witness_7 (by decide +kernel)
theorem positive_7 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_7 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_7 ρ hρ u
noncomputable def polynomial_8 : BiPoly := r7_rat_grid%[[74287684318355280,2967945206856127200,12335614758405025200],[0,2128489721240049000,12365882225511300000],[569173111215814980,47408337806475033450,125642885926008710700],[0,12790492725271375800,52744418094555270000],[1768800375055780920,221794323235310343375,402523275260070532800],[0,13236796986446682000,79337962068571575000],[2832070053437658000,401059977039737392500,556142653149851970000],[0,-2076604255101636000,48397620761215200000],[2435665493701553040,308843512503326406000,336177226437766833600],[0,-2471264010826214400,9482525288121600000],[1045860053051694240,88181796924647841600,69502722294313281600],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
noncomputable def witness_8 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_0, 1656000, by norm_num, R7.Core.Certificates.Terminal002.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_1, 894240000, by norm_num, R7.Core.Certificates.Terminal002.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_2, 1458000, by norm_num, R7.Core.Certificates.Terminal002.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_3, 1968300000000, by norm_num, R7.Core.Certificates.Terminal002.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_4, 3259504800000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_5, 1652994086400000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_6, 5487718865640422400000000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_6⟩
theorem bound_8 : minorBindings polynomial_8 witness_8 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_8 witness_8 (by decide +kernel)
theorem positive_8 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_8 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_8 ρ hρ u
noncomputable def polynomial_9 : BiPoly := r7_rat_grid%[[48186606044338560,2434460942013770025,9093751625603570400],[0,901693193191263000,7373247000758100000],[349988434846991820,32364752754557562300,82707893693442838800],[0,5347628113428279900,28932992677696185000],[1026454103659313280,133995184333032337875,243015508997172632700],[0,5073718478652288000,39693640693952925000],[1544765483693268000,221993077954141800000,309697843237021620000],[0,-1206209636977117500,22000945225401000000],[1244011438743527520,158625317001772503000,172957726567153756800],[0,-1032553597116045600,3962027348393400000],[498720303075576420,42049653163142257800,33142501834788277800],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
noncomputable def witness_9 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_8, 310500, by norm_num, R7.Core.Certificates.Terminal002.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_9, 335340000, by norm_num, R7.Core.Certificates.Terminal002.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_10, 314928000, by norm_num, R7.Core.Certificates.Terminal002.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_11, 1700611200000000, by norm_num, R7.Core.Certificates.Terminal002.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_12, 51656065200000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_13, 2789427520800000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_14, 4115789149230316800000000000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_14⟩
theorem bound_9 : minorBindings polynomial_9 witness_9 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_9 witness_9 (by decide +kernel)
theorem positive_9 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_9 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_9 ρ hρ u
noncomputable def polynomial_10 : BiPoly := r7_rat_grid%[[22888637871060816,1377691717037196465,4758378606016633440],[0,209809443365852400,3223159407731880000],[154843368144426684,15477093763338815010,38529686898153241560],[0,1489189403571015600,11508617912174640000],[421579364002932240,56646785413868131125,102683419307328464100],[0,1330535348357443200,14305749899722470000],[587010883803441840,85201488822744208800,119341546835134193100],[0,-467438581385596800,7180494058857510000],[436660580771086680,55878816058331089500,60993623815154071200],[0,-308908001353276800,1185315661015200000],[161720952647808276,13635518598533508840,10747180206620664840],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
noncomputable def witness_10 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_16, 62100, by norm_num, R7.Core.Certificates.Terminal002.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_17, 154256400, by norm_num, R7.Core.Certificates.Terminal002.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_18, 7243344, by norm_num, R7.Core.Certificates.Terminal002.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_19, 1173421728000, by norm_num, R7.Core.Certificates.Terminal002.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_20, 63364773312000000, by norm_num, R7.Core.Certificates.Terminal002.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_21, 684339551769600000000, by norm_num, R7.Core.Certificates.Terminal002.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_22, 302922081383351316480000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_22⟩
theorem bound_10 : minorBindings polynomial_10 witness_10 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_10 witness_10 (by decide +kernel)
theorem positive_10 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_10 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_10 ρ hρ u
noncomputable def polynomial_11 : BiPoly := r7_rat_grid%[[7227990906650784,485890651982423160,1603433607761410560],[0,22932613210993200,941284521978840000],[44543982616889868,4653677678882717520,11420786745805893120],[0,285633165480219000,3024594972622350000],[109977225392069280,15001846489373976000,27186767208807235200],[0,245264831701426800,3379974177698280000],[139028893532394120,20277301439462288400,28457405799002290800],[0,-108510521756880600,1530715853917170000],[94243290813903600,12080141316603765000,13192452202429224000],[0,-60065444707581600,230478045197400000],[31956834954357324,2694443794919795160,2123694292326239160],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
noncomputable def witness_11 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal002.polynomial_24, 13413600, by norm_num, R7.Core.Certificates.Terminal002.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal002.polynomial_25, 8692012800, by norm_num, R7.Core.Certificates.Terminal002.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal002.polynomial_26, 1836660096, by norm_num, R7.Core.Certificates.Terminal002.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal002.polynomial_27, 1785233613312000, by norm_num, R7.Core.Certificates.Terminal002.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal002.polynomial_28, 723019613391360000000, by norm_num, R7.Core.Certificates.Terminal002.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal002.polynomial_29, 23425835473880064000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal002.polynomial_30, 1885348720274625758822400000000000, by norm_num, R7.Core.Certificates.Terminal002.positive_30⟩
theorem bound_11 : minorBindings polynomial_11 witness_11 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_11 witness_11 (by decide +kernel)
theorem positive_11 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_11 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_11 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry001
