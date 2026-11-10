import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch13
import R7.Certificates.Spectral.Terminal.Batches.Batch14
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.CriticalQ8001
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_6 : BiPoly := r7_rat_grid%[[152834384538],[121074907500],[1125406928547],[259544299500],[2052227674872],[130913640000],[1088433017880],[0],[12964882392]]
noncomputable def witness_6 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_7, 305668769076, by norm_num, R7.Core.Certificates.Terminal109.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_8, 673344367890993194175144, by norm_num, R7.Core.Certificates.Terminal109.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_9, 2743121053318233684797780004642563136, by norm_num, R7.Core.Certificates.Terminal109.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_10, 5959867020532584026671255683294385850487433743360, by norm_num, R7.Core.Certificates.Terminal109.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_11, 154537949986328802219301242361746623330876948713109421834240, by norm_num, R7.Core.Certificates.Terminal109.positive_11⟩
theorem bound_6 : ordinaryBindings polynomial_6 witness_6 := by
 decide +kernel
theorem positive_6 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_6 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_6 ρ hρ u
noncomputable def polynomial_7 : BiPoly := r7_rat_grid%[[81813013056],[49874980500],[493215627780],[91590394500],[766965627504],[38679030000],[351647590392],[0],[3704252112]]
noncomputable def witness_7 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_12, 163626026112, by norm_num, R7.Core.Certificates.Terminal109.positive_12⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_13, 158918312700078124932720, by norm_num, R7.Core.Certificates.Terminal109.positive_13⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_14, 242397140776267489740259168075061760, by norm_num, R7.Core.Certificates.Terminal109.positive_14⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_15, 170238988442956221050876026218649429533165219840, by norm_num, R7.Core.Certificates.Terminal109.positive_15⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_16, 1261216264969128346702492759141199046271644879274528604160, by norm_num, R7.Core.Certificates.Terminal109.positive_16⟩
theorem bound_7 : ordinaryBindings polynomial_7 witness_7 := by
 decide +kernel
theorem positive_7 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_7 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_7 ρ hρ u
noncomputable def polynomial_8 : BiPoly := r7_rat_grid%[[20453253264],[11083329000],[98643125556],[16652799000],[127827604584],[5950620000],[50235370056],[0],[463031514]]
noncomputable def witness_8 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_17, 40906506528, by norm_num, R7.Core.Certificates.Terminal109.positive_17⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_18, 7947451137275434259136, by norm_num, R7.Core.Certificates.Terminal109.positive_18⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_19, 2020463265765692168160377466958848, by norm_num, R7.Core.Certificates.Terminal109.positive_19⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_20, 202716021402350759916353382544023406006910976, by norm_num, R7.Core.Certificates.Terminal109.positive_20⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_21, 187727812603973751046239240156760658669633367360995328, by norm_num, R7.Core.Certificates.Terminal109.positive_21⟩
theorem bound_8 : ordinaryBindings polynomial_8 witness_8 := by
 decide +kernel
theorem positive_8 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_8 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_8 ρ hρ u
noncomputable def polynomial_9 : BiPoly := r7_rat_grid%[[1970514616],[21726441000],[81692547120],[80746776000],[269627212224],[77358060000],[234431726928],[0],[3704252112]]
noncomputable def witness_9 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_22, 3941029232, by norm_num, R7.Core.Certificates.Terminal109.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_23, 171867193946433823680, by norm_num, R7.Core.Certificates.Terminal109.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_24, 66984469289866610704125481328640, by norm_num, R7.Core.Certificates.Terminal109.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_25, 30378070028289011396472894369986542211235840, by norm_num, R7.Core.Certificates.Terminal109.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_26, 225056060121546940423553576641551116795095020900188160, by norm_num, R7.Core.Certificates.Terminal109.positive_26⟩
theorem bound_9 : ordinaryBindings polynomial_9 witness_9 := by
 decide +kernel
theorem positive_9 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_9 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_9 ρ hρ u
noncomputable def polynomial_10 : BiPoly := r7_rat_grid%[[22888895004],[126616648500],[561086614068],[477230982000],[1788200079456],[473074290000],[1574041595088],[0],[25929764784]]
noncomputable def witness_10 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal109.polynomial_27, 45777790008, by norm_num, R7.Core.Certificates.Terminal109.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal109.polynomial_28, 35338834712836733015088, by norm_num, R7.Core.Certificates.Terminal109.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal109.polynomial_29, 115959949409056969519662205501664256, by norm_num, R7.Core.Certificates.Terminal109.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal109.polynomial_30, 357142761567167054940796791381105355644949549056, by norm_num, R7.Core.Certificates.Terminal109.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal109.polynomial_31, 18521255603489673903697731692107960747592416849137898487808, by norm_num, R7.Core.Certificates.Terminal109.positive_31⟩
theorem bound_10 : ordinaryBindings polynomial_10 witness_10 := by
 decide +kernel
theorem positive_10 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_10 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_10 ρ hρ u
noncomputable def polynomial_11 : BiPoly := r7_rat_grid%[[117073327224],[351130589250],[1940912894658],[1251680548500],[5658900507072],[1187148690000],[4722124785264],[0],[77789294352]]
noncomputable def witness_11 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_0, 234146654448, by norm_num, R7.Core.Certificates.Terminal110.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_1, 785623831011256086715068, by norm_num, R7.Core.Certificates.Terminal110.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_2, 8524695645470496227618582682657921792, by norm_num, R7.Core.Certificates.Terminal110.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_3, 79402156230288166934570039345355491913438212146176, by norm_num, R7.Core.Certificates.Terminal110.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_4, 12353275406362753830911564630392159489068401578007013030395904, by norm_num, R7.Core.Certificates.Terminal110.positive_4⟩
theorem bound_11 : ordinaryBindings polynomial_11 witness_11 := by
 decide +kernel
theorem positive_11 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_11 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_11 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8001

namespace R7.Core.SpectralSliceCertificates.CriticalQ8002
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_12 : BiPoly := r7_rat_grid%[[333356659880],[595166587500],[4127643512910],[1929123465000],[10818578033952],[1606667400000],[8205110442480],[0],[129648823920]]
noncomputable def witness_12 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_5, 666713319760, by norm_num, R7.Core.Certificates.Terminal110.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_6, 5149686551679713879953200, by norm_num, R7.Core.Certificates.Terminal110.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_7, 108943386437041988148100800897542092800, by norm_num, R7.Core.Certificates.Terminal110.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_8, 1774491736825434314155637132054520789565266444288000, by norm_num, R7.Core.Certificates.Terminal110.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_9, 460121533470351426346980324018300707372653205166758803537920000, by norm_num, R7.Core.Certificates.Terminal110.positive_9⟩
theorem bound_12 : ordinaryBindings polynomial_12 witness_12 := by
 decide +kernel
theorem positive_12 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_12 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_12 ρ hρ u
noncomputable def polynomial_13 : BiPoly := r7_rat_grid%[[573858693060],[672950561250],[5682112839150],[1899819315000],[13192107701184],[1309136400000],[8874915376560],[0],[129648823920]]
noncomputable def witness_13 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_10, 1147717386120, by norm_num, R7.Core.Certificates.Terminal110.positive_10⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_11, 12590056932889570003633500, by norm_num, R7.Core.Certificates.Terminal110.positive_11⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_12, 328036302270272667401291854267504128000, by norm_num, R7.Core.Certificates.Terminal110.positive_12⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_13, 5801011526750093345286116037840183760080948879360000, by norm_num, R7.Core.Certificates.Terminal110.positive_13⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_14, 1504188643979026443933126840421260082822356932413331924582400000, by norm_num, R7.Core.Certificates.Terminal110.positive_14⟩
theorem bound_13 : ordinaryBindings polynomial_13 witness_13 := by
 decide +kernel
theorem positive_13 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_13 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_13 ρ hρ u
noncomputable def polynomial_14 : BiPoly := r7_rat_grid%[[611337538152],[511727382000],[4988850665070],[1222783902000],[10093030235424],[687296610000],[5927773666608],[0],[77789294352]]
noncomputable def witness_14 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_15, 1222675076304, by norm_num, R7.Core.Certificates.Terminal110.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_16, 11937621821678872871002560, by norm_num, R7.Core.Certificates.Terminal110.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_17, 239145411620566490450465838911797370880, by norm_num, R7.Core.Certificates.Terminal110.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_18, 2829560693421307969553395116742247643897968095150080, by norm_num, R7.Core.Certificates.Terminal110.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_19, 440219059334798711184865013434444210570515033616668633472696320, by norm_num, R7.Core.Certificates.Terminal110.positive_19⟩
theorem bound_14 : ordinaryBindings polynomial_14 witness_14 := by
 decide +kernel
theorem positive_14 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_14 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_14 ρ hρ u
noncomputable def polynomial_15 : BiPoly := r7_rat_grid%[[381794060928],[245680459500],[2564721264456],[502359436500],[4431356958912],[235049490000],[2243846529168],[0],[25929764784]]
noncomputable def witness_15 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_20, 763588121856, by norm_num, R7.Core.Certificates.Terminal110.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_21, 3856422498640073918850672, by norm_num, R7.Core.Certificates.Terminal110.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_22, 33985666432707599985672834398479177728, by norm_num, R7.Core.Certificates.Terminal110.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_23, 152304178689507679566393291670447173617595615940608, by norm_num, R7.Core.Certificates.Terminal110.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_24, 7898423058078478999836442328500403312003729369939132707897344, by norm_num, R7.Core.Certificates.Terminal110.positive_24⟩
theorem bound_15 : ordinaryBindings polynomial_15 witness_15 := by
 decide +kernel
theorem positive_15 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_15 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_15 ρ hρ u
noncomputable def polynomial_16 : BiPoly := r7_rat_grid%[[109084017408],[62805531000],[591858753336],[105467727000],[852184030560],[41654340000],[368392713744],[0],[3704252112]]
noncomputable def witness_16 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_25, 218168034816, by norm_num, R7.Core.Certificates.Terminal110.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_26, 254304787483733647292352, by norm_num, R7.Core.Certificates.Terminal110.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal110.polynomial_27, 431002178218146203710863962380554240, by norm_num, R7.Core.Certificates.Terminal110.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal110.polynomial_28, 317114883948444897728543879467430636525570949120, by norm_num, R7.Core.Certificates.Terminal110.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal110.polynomial_29, 2349346957225323823053165336403806741126701060567209082880, by norm_num, R7.Core.Certificates.Terminal110.positive_29⟩
theorem bound_16 : ordinaryBindings polynomial_16 witness_16 := by
 decide +kernel
theorem positive_16 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_16 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_16 ρ hρ u
noncomputable def polynomial_17 : BiPoly := r7_rat_grid%[[15992093848],[50574105000],[275162699148],[194617266000],[844504836672],[202321080000],[753530550840],[0],[12964882392]]
noncomputable def witness_17 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal110.polynomial_30, 31984187696, by norm_num, R7.Core.Certificates.Terminal110.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal110.polynomial_31, 15043970736424197566016, by norm_num, R7.Core.Certificates.Terminal110.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_0, 24197982837046847127011561859477504, by norm_num, R7.Core.Certificates.Terminal111.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_1, 35852031491463840484332452583750856265016606720, by norm_num, R7.Core.Certificates.Terminal111.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_2, 929634743602218087600037132754492763410473380103433748480, by norm_num, R7.Core.Certificates.Terminal111.positive_2⟩
theorem bound_17 : ordinaryBindings polynomial_17 witness_17 := by
 decide +kernel
theorem positive_17 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_17 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_17 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8002

namespace R7.Core.SpectralSliceCertificates.CriticalQ8003
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_18 : BiPoly := r7_rat_grid%[[109595502126],[265151279250],[1741231368252],[989117113500],[5159926616976],[999704160000],[4470947934984],[0],[77789294352]]
noncomputable def witness_18 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_3, 219191004252, by norm_num, R7.Core.Certificates.Terminal111.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_4, 693019303596568339052508, by norm_num, R7.Core.Certificates.Terminal111.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_5, 6937411398429520160800770506009351616, by norm_num, R7.Core.Certificates.Terminal111.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_6, 61341001013296883068924306909791679625851126668288, by norm_num, R7.Core.Certificates.Terminal111.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_7, 9543346367339363006025356028426744954831629041860584591818752, by norm_num, R7.Core.Certificates.Terminal111.positive_7⟩
theorem bound_18 : ordinaryBindings polynomial_18 witness_18 := by
 decide +kernel
theorem positive_18 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_18 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_18 ρ hρ u
noncomputable def polynomial_19 : BiPoly := r7_rat_grid%[[417229603155],[631192023750],[5292893911875],[2181570817500],[14436645111936],[1963704600000],[11554135112880],[0],[194473235880]]
noncomputable def witness_19 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_8, 834459206310, by norm_num, R7.Core.Certificates.Terminal111.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_9, 8435004734726866603800000, by norm_num, R7.Core.Certificates.Terminal111.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_10, 239574938740012573585413180813476100000, by norm_num, R7.Core.Certificates.Terminal111.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_11, 5503635900363983073657503095805216649797364336000000, by norm_num, R7.Core.Certificates.Terminal111.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_12, 2140619765298242116279446027764716272141092377434455151360000000, by norm_num, R7.Core.Certificates.Terminal111.positive_12⟩
theorem bound_19 : ordinaryBindings polynomial_19 witness_19 := by
 decide +kernel
theorem positive_19 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_19 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_19 ρ hρ u
noncomputable def polynomial_20 : BiPoly := r7_rat_grid%[[906431149930],[895439970000],[9455864426670],[2705086417500],[23127286748832],[2023210800000],[16577672118480],[0],[259297647840]]
noncomputable def witness_20 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_13, 1812862299860, by norm_num, R7.Core.Certificates.Terminal111.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_14, 33482547523521072142532400, by norm_num, R7.Core.Certificates.Terminal111.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_15, 1535455348985581247495989885834319313600, by norm_num, R7.Core.Certificates.Terminal111.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_16, 50771493800719118056814849361328149928416182950656000, by norm_num, R7.Core.Certificates.Terminal111.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_17, 26329857839699218025302723843552631069634361231392423169966080000, by norm_num, R7.Core.Certificates.Terminal111.positive_17⟩
theorem bound_20 : ordinaryBindings polynomial_20 witness_20 := by
 decide +kernel
theorem positive_20 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_20 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_20 ρ hρ u
noncomputable def polynomial_21 : BiPoly := r7_rat_grid%[[1181122944645],[805897796250],[10222364906955],[2052801112500],[21963310406784],[1249630200000],[13814726765400],[0],[194473235880]]
noncomputable def witness_21 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_18, 2362245889290, by norm_num, R7.Core.Certificates.Terminal111.positive_18⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_19, 47646007702552997647961400, by norm_num, R7.Core.Certificates.Terminal111.positive_19⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_20, 2082973627388313927797253266348097775200, by norm_num, R7.Core.Certificates.Terminal111.positive_20⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_21, 57477020198990527035278185742783659605607264676160000, by norm_num, R7.Core.Certificates.Terminal111.positive_21⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_22, 22355484213675618604034343394749639284581778708016910985241600000, by norm_num, R7.Core.Certificates.Terminal111.positive_22⟩
theorem bound_21 : ordinaryBindings polynomial_21 witness_21 := by
 decide +kernel
theorem positive_21 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_21 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_21 ρ hρ u
noncomputable def polynomial_22 : BiPoly := r7_rat_grid%[[873488843616],[444588506250],[6267054827436],[982787967000],[11558736949968],[499852080000],[6279421257000],[0],[77789294352]]
noncomputable def witness_22 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_23, 1746977687232, by norm_num, R7.Core.Certificates.Terminal111.positive_23⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_24, 21699150956490961991931804, by norm_num, R7.Core.Certificates.Terminal111.positive_24⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_25, 499942198726157406127928304442783964544, by norm_num, R7.Core.Certificates.Terminal111.positive_25⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_26, 6273273761429204514049610561098955976371830223616000, by norm_num, R7.Core.Certificates.Terminal111.positive_26⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_27, 975987078356989228305224550936589134091755716531670011633664000, by norm_num, R7.Core.Certificates.Terminal111.positive_27⟩
theorem bound_22 : ordinaryBindings polynomial_22 witness_22 := by
 decide +kernel
theorem positive_22 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_22 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_22 ρ hρ u
noncomputable def polynomial_23 : BiPoly := r7_rat_grid%[[291162947872],[134414173500],[1690067613804],[248002302000],[2601489960384],[107111160000],[1205648881344],[0],[12964882392]]
noncomputable def witness_23 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_28, 582325895744, by norm_num, R7.Core.Certificates.Terminal111.positive_28⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_29, 1950273104114989816250352, by norm_num, R7.Core.Certificates.Terminal111.positive_29⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_30, 10111415763934197135866105140036110336, by norm_num, R7.Core.Certificates.Terminal111.positive_30⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_31, 24359259114750386620345460777947093804675511943168, by norm_num, R7.Core.Certificates.Terminal111.positive_31⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_0, 631629859157985589938618506794265796751619664131129015795712, by norm_num, R7.Core.Certificates.Terminal112.positive_0⟩
theorem bound_23 : ordinaryBindings polynomial_23 witness_23 := by
 decide +kernel
theorem positive_23 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_23 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_23 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8003

namespace R7.Core.SpectralSliceCertificates.CriticalQ8004
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_24 : BiPoly := r7_rat_grid%[[41079480388],[75619309500],[610495513872],[270176877000],[1750941404640],[261827280000],[1473570854976],[0],[25929764784]]
noncomputable def witness_24 : Fin 5 → MinorWitness
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
noncomputable def polynomial_25 : BiPoly := r7_rat_grid%[[273349707230],[310782978750],[3425527640040],[1080085492500],[9389880904128],[952099200000],[7535305508400],[0],[129648823920]]
noncomputable def witness_25 : Fin 5 → MinorWitness
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
noncomputable def polynomial_26 : BiPoly := r7_rat_grid%[[822127921920],[568542150000],[8773828149840],[1724404695000],[21906285099936],[1279383300000],[16075318417920],[0],[259297647840]]
noncomputable def witness_26 : Fin 5 → MinorWitness
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
noncomputable def polynomial_27 : BiPoly := r7_rat_grid%[[1376604223140],[580026495000],[12299692502580],[1429034107500],[27248486871072],[862839900000],[17749830753120],[0],[259297647840]]
noncomputable def witness_27 : Fin 5 → MinorWitness
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
noncomputable def polynomial_28 : BiPoly := r7_rat_grid%[[1242778412790],[340131371250],[9287374125300],[746069415000],[17762686510464],[386790300000],[10047074011200],[0],[129648823920]]
noncomputable def witness_28 : Fin 5 → MinorWitness
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
noncomputable def polynomial_29 : BiPoly := r7_rat_grid%[[497111365116],[127159119000],[2995493174664],[246212619000],[4781545239840],[113061780000],[2310827022576],[0],[25929764784]]
noncomputable def witness_29 : Fin 5 → MinorWitness
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

namespace R7.Core.SpectralSliceCertificates.CriticalQ8005
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_30 : BiPoly := r7_rat_grid%[[85325503130],[60867352500],[949644427680],[202321650000],[2506263696264],[148765500000],[1925689185480],[0],[32412205980]]
noncomputable def witness_30 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal112.polynomial_31, 170651006260, by norm_num, R7.Core.Certificates.Terminal112.positive_31⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_0, 320410719745228338303600, by norm_num, R7.Core.Certificates.Terminal113.positive_0⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_1, 1599082072749750960351815524835500800, by norm_num, R7.Core.Certificates.Terminal113.positive_1⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_2, 6151579042991253181918258964391448593079776768000, by norm_num, R7.Core.Certificates.Terminal113.positive_2⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_3, 398772494087367546941330042153674234298965854353669345280000, by norm_num, R7.Core.Certificates.Terminal113.positive_3⟩
theorem bound_30 : ordinaryBindings polynomial_30 witness_30 := by
 decide +kernel
theorem positive_30 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_30 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_30 ρ hρ u
noncomputable def polynomial_31 : BiPoly := r7_rat_grid%[[431861354590],[156272546250],[4537558061340],[435962752500],[11225791621728],[252901350000],[8121384825720],[0],[129648823920]]
noncomputable def witness_31 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_4, 863722709180, by norm_num, R7.Core.Certificates.Terminal113.positive_4⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_5, 7813962774892808453139900, by norm_num, R7.Core.Certificates.Terminal113.positive_5⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_6, 175271673522007860833122994321952494400, by norm_num, R7.Core.Certificates.Terminal113.positive_6⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_7, 2846397645469865324397054180776946652137976551936000, by norm_num, R7.Core.Certificates.Terminal113.positive_7⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_8, 738064214287650310217734715300500410596540027054078398218240000, by norm_num, R7.Core.Certificates.Terminal113.positive_8⟩
theorem bound_31 : ordinaryBindings polynomial_31 witness_31 := by
 decide +kernel
theorem positive_31 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_31 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_31 ρ hρ u
noncomputable def polynomial_32 : BiPoly := r7_rat_grid%[[1021512346020],[115115167500],[9144630332760],[139806315000],[20382112615896],[0],[13312373064840],[0],[194473235880]]
noncomputable def witness_32 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_9, 2043024692040, by norm_num, R7.Core.Certificates.Terminal113.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_10, 37352159637024730390210800, by norm_num, R7.Core.Certificates.Terminal113.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_11, 1522591915773826955000117776368741753600, by norm_num, R7.Core.Certificates.Terminal113.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_12, 40538623216581255762381445290317824768693016206848000, by norm_num, R7.Core.Certificates.Terminal113.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_13, 15767354470097301758128432080958586832821086760206027950612480000, by norm_num, R7.Core.Certificates.Terminal113.positive_13⟩
theorem bound_32 : ordinaryBindings polynomial_32 witness_32 := by
 decide +kernel
theorem positive_32 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_32 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_32 ρ hρ u
noncomputable def polynomial_33 : BiPoly := r7_rat_grid%[[1179301982860],[-22233573750],[8993205943200],[-130537867500],[17426470232592],[-104135850000],[9963348394440],[0],[129648823920]]
noncomputable def witness_33 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_14, 2358603965720, by norm_num, R7.Core.Certificates.Terminal113.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_15, 42422328072534689445145500, by norm_num, R7.Core.Certificates.Terminal113.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_16, 1478502683776918413455012524848814272000, by norm_num, R7.Core.Certificates.Terminal113.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_17, 29461214641765396300909867025251122413964164895360000, by norm_num, R7.Core.Certificates.Terminal113.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_18, 7639223659119135485931365371494793927260810727416747730022400000, by norm_num, R7.Core.Certificates.Terminal113.positive_18⟩
theorem bound_33 : ordinaryBindings polynomial_33 witness_33 := by
 decide +kernel
theorem positive_33 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_33 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_33 ρ hρ u
noncomputable def polynomial_34 : BiPoly := r7_rat_grid%[[589650991430],[0],[3597282377280],[0],[5808823410864],[0],[2846670969840],[0],[32412205980]]
noncomputable def witness_34 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_19, 1179301982860, by norm_num, R7.Core.Certificates.Terminal113.positive_19⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_20, 8484564480867277226841600, by norm_num, R7.Core.Certificates.Terminal113.positive_20⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_21, 98570673574894001539413387931694284800, by norm_num, R7.Core.Certificates.Terminal113.positive_21⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_22, 561196549886451134474800724016392642772002340864000, by norm_num, R7.Core.Certificates.Terminal113.positive_22⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_23, 36379236340369999563603840372544902468165396098252278333440000, by norm_num, R7.Core.Certificates.Terminal113.positive_23⟩
theorem bound_34 : ordinaryBindings polynomial_34 witness_34 := by
 decide +kernel
theorem positive_34 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_34 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_34 ρ hρ u
noncomputable def polynomial_35 : BiPoly := r7_rat_grid%[[104484139332],[13815136500],[1055307682392],[12527781000],[2485305691680],[-17851860000],[1708002581904],[0],[25929764784]]
noncomputable def witness_35 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal113.polynomial_24, 208968278664, by norm_num, R7.Core.Certificates.Terminal113.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal113.polynomial_25, 440860801704189291918576, by norm_num, R7.Core.Certificates.Terminal113.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal113.polynomial_26, 2191314922839545626865438211737295360, by norm_num, R7.Core.Certificates.Terminal113.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal113.polynomial_27, 7485402594503061789756943802326197166970078330880, by norm_num, R7.Core.Certificates.Terminal113.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal113.polynomial_28, 388189457178015447152431226650049769161482610171547447459840, by norm_num, R7.Core.Certificates.Terminal113.positive_28⟩
theorem bound_35 : ordinaryBindings polynomial_35 witness_35 := by
 decide +kernel
theorem positive_35 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_35 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_35 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8005

namespace R7.Core.SpectralSliceCertificates.CriticalQ8006
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_36 : BiPoly := r7_rat_grid%[[457523961222],[-72186603750],[3989799974988],[-308895259500],[8720221117824],[-241000110000],[5525890706160],[0],[77789294352]]
noncomputable def witness_36 : Fin 5 → MinorWitness
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
noncomputable def polynomial_37 : BiPoly := r7_rat_grid%[[745667047674],[-232084664250],[5690091748020],[-608099989500],[10926584928576],[-348111270000],[6128715146832],[0],[77789294352]]
noncomputable def witness_37 : Fin 5 → MinorWitness
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
noncomputable def polynomial_38 : BiPoly := r7_rat_grid%[[100265917408],[-30969769500],[802279483800],[-109228977000],[1664087526768],[-71407440000],[987962277768],[0],[12964882392]]
noncomputable def witness_38 : Fin 5 → MinorWitness
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
noncomputable def polynomial_39 : BiPoly := r7_rat_grid%[[291162947872],[-160275274500],[2183283241584],[-381224694000],[4050202812336],[-196370460000],[2160120912408],[0],[25929764784]]
noncomputable def witness_39 : Fin 5 → MinorWitness
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
noncomputable def polynomial_40 : BiPoly := r7_rat_grid%[[54542008704],[-36944430000],[394572502224],[-77713062000],[681747224448],[-35703720000],[334902467040],[0],[3704252112]]
noncomputable def witness_40 : Fin 5 → MinorWitness
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
noncomputable def polynomial_41 : BiPoly := r7_rat_grid%[[985257308],[13277269500],[57184782984],[62395236000],[224689343520],[68432130000],[217686603576],[0],[3704252112]]
noncomputable def witness_41 : Fin 5 → MinorWitness
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

namespace R7.Core.SpectralSliceCertificates.CriticalQ8007
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_42 : BiPoly := r7_rat_grid%[[11444447502],[75982081500],[370405108866],[365241117000],[1433354464176],[422494020000],[1440080608272],[0],[25929764784]]
noncomputable def witness_42 : Fin 5 → MinorWitness
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
noncomputable def polynomial_43 : BiPoly := r7_rat_grid%[[58536663612],[207204341250],[1256478705132],[941130283500],[4433241523824],[1062185670000],[4270006454760],[0],[77789294352]]
noncomputable def witness_43 : Fin 5 → MinorWitness
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
noncomputable def polynomial_44 : BiPoly := r7_rat_grid%[[166678329940],[348453720000],[2652915193380],[1430387130000],[8395204073568],[1428148800000],[7367854274880],[0],[129648823920]]
noncomputable def witness_44 : Fin 5 → MinorWitness
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
noncomputable def polynomial_45 : BiPoly := r7_rat_grid%[[286929346530],[390839786250],[3652555940760],[1394531685000],[10231114791168],[1145494350000],[7953933592200],[0],[129648823920]]
noncomputable def witness_45 : Fin 5 → MinorWitness
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
noncomputable def polynomial_46 : BiPoly := r7_rat_grid%[[305668769076],[297005319000],[3225259758858],[888302007000],[7872694421616],[589111380000],[5324949225936],[0],[77789294352]]
noncomputable def witness_46 : Fin 5 → MinorWitness
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
noncomputable def polynomial_47 : BiPoly := r7_rat_grid%[[190897030464],[142236055500],[1676933134452],[363586111500],[3493954525296],[199345770000],[2026159925592],[0],[25929764784]]
noncomputable def witness_47 : Fin 5 → MinorWitness
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

namespace R7.Core.SpectralSliceCertificates.CriticalQ8008
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_48 : BiPoly := r7_rat_grid%[[15992093848],[59023276500],[340516736844],[293715582000],[1293883523712],[365963130000],[1356354991512],[0],[25929764784]]
noncomputable def witness_48 : Fin 5 → MinorWitness
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
noncomputable def polynomial_49 : BiPoly := r7_rat_grid%[[109595502126],[307336674750],[2147102142792],[1479239644500],[7747693664400],[1832790960000],[7937188468848],[0],[155578588704]]
noncomputable def witness_49 : Fin 5 → MinorWitness
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
noncomputable def polynomial_50 : BiPoly := r7_rat_grid%[[417229603155],[732932876250],[6541913774190],[3253679100000],[21562887808368],[3629878200000],[20345324872680],[0],[388946471760]]
noncomputable def witness_50 : Fin 5 → MinorWitness
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
noncomputable def polynomial_51 : BiPoly := r7_rat_grid%[[906431149930],[1040411985000],[11745394640340],[4060837935000],[34652285063712],[3748890600000],[29136514632480],[0],[518595295680]]
noncomputable def witness_51 : Fin 5 → MinorWitness
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
noncomputable def polynomial_52 : BiPoly := r7_rat_grid%[[1181122944645],[943036556250],[12803448011250],[3102156540000],[33187466553696],[2305865250000],[24364154477160],[0],[388946471760]]
noncomputable def witness_52 : Fin 5 → MinorWitness
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
noncomputable def polynomial_53 : BiPoly := r7_rat_grid%[[873488843616],[522171809250],[7943987961888],[1490698336500],[17694461970000],[916395480000],[11152252152432],[0],[155578588704]]
noncomputable def witness_53 : Fin 5 → MinorWitness
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
