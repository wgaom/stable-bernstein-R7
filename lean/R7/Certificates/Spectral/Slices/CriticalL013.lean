import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal074
import R7.Certificates.Spectral.Terminal.Terminal075
import R7.Certificates.Spectral.Terminal.Terminal076

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL013
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_78 : BiPoly := [[6078248035067145880],[-151421616650000],[67099493834112944860],[-1982322984741622500],[258382023050144318280],[-2396589834592125000],[418494250755905462100],[1351081277247487500],[298631027108033201160],[950599260891540000],[80644793135986087920],[0],[169881979092154560]]
def witness_78 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal074.polynomial_26, 607824803506714588000, by norm_num, R7.Core.Certificates.Terminal074.positive_26⟩
 | 1 => ⟨R7.Core.Certificates.Terminal074.polynomial_27, 3996904192144410095746914597403508532640000, by norm_num, R7.Core.Certificates.Terminal074.positive_27⟩
 | 2 => ⟨R7.Core.Certificates.Terminal074.polynomial_28, 103237241655845928836114670990435743654114917285304250890920912000, by norm_num, R7.Core.Certificates.Terminal074.positive_28⟩
 | 3 => ⟨R7.Core.Certificates.Terminal074.polynomial_29, 4320361817711643316102037152836739876440108041068588819453433080863934617991343520000000, by norm_num, R7.Core.Certificates.Terminal074.positive_29⟩
 | 4 => ⟨R7.Core.Certificates.Terminal074.polynomial_30, 129018937581682145014254838976239536602783566478069507413138134245580111750816676645097889305000998320000000000, by norm_num, R7.Core.Certificates.Terminal074.positive_30⟩
 | 5 => ⟨R7.Core.Certificates.Terminal074.polynomial_31, 1040460793071852408174264708186490806005441748230733677441046907256594434683278466475839240746955751576187783033049229440000000000000, by norm_num, R7.Core.Certificates.Terminal074.positive_31⟩
 | 6 => ⟨R7.Core.Certificates.Terminal075.polynomial_0, 17675553869483898287934747255681832669596398713013362765946674495834132704197385131968699233950599716496492848324991712447837895738224640000000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_0⟩
theorem bound_78 : minorBindings polynomial_78 witness_78 := by
 decide +kernel
theorem positive_78 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_78 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_78 ρ hρ u
def polynomial_79 : BiPoly := [[323796804549947520],[46138126320600000],[4158131529522620280],[-107852104245000],[18568667934737832480],[-106631677698750000],[34327049063963711400],[129958811465175000],[27539801304095772720],[101352703856040000],[8230847507907374880],[0],[18875775454683840]]
def witness_79 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal075.polynomial_1, 32379680454994752000, by norm_num, R7.Core.Certificates.Terminal075.positive_1⟩
 | 1 => ⟨R7.Core.Certificates.Terminal075.polynomial_2, 13189297264395600999435736983499514880000, by norm_num, R7.Core.Certificates.Terminal075.positive_2⟩
 | 2 => ⟨R7.Core.Certificates.Terminal075.polynomial_3, 24483722370326502512677772250204614005330923784428738136704000, by norm_num, R7.Core.Certificates.Terminal075.positive_3⟩
 | 3 => ⟨R7.Core.Certificates.Terminal075.polynomial_4, 84045018991315322525165195884508748884203136137467226213170872653830840322560000000, by norm_num, R7.Core.Certificates.Terminal075.positive_4⟩
 | 4 => ⟨R7.Core.Certificates.Terminal075.polynomial_5, 231457278580095606274048987116277862181642486743311731506433860927805139196185898594550324856320000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_5⟩
 | 5 => ⟨R7.Core.Certificates.Terminal075.polynomial_6, 190506798104849314077786090210130399536442823366001658521526714885929343413201805230005160873036516256508197724160000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_6⟩
 | 6 => ⟨R7.Core.Certificates.Terminal075.polynomial_7, 359596354361792456985423148318996233763849599618543282437453046961244233908484513690870416238907061321168669762832855670032957440000000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_7⟩
theorem bound_79 : minorBindings polynomial_79 witness_79 := by
 decide +kernel
theorem positive_79 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_79 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_79 ρ hρ u
def polynomial_80 : BiPoly := [[1434998807695319220],[74787914417850000],[17117433489422285280],[-493960310025142500],[71242187954938108020],[-789886879236225000],[123216523245962721000],[525185195986687500],[92749462784957994480],[385919910836460000],[26093537844216996960],[0],[56627326364051520]]
def witness_80 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal075.polynomial_8, 143499880769531922000, by norm_num, R7.Core.Certificates.Terminal075.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal075.polynomial_9, 240708284071266659443389301036519399680000, by norm_num, R7.Core.Certificates.Terminal075.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal075.polynomial_10, 1714276265115035058129191590728888474770476465848936698872704000, by norm_num, R7.Core.Certificates.Terminal075.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal075.polynomial_11, 21122340669501928840634147086923184475297856719354281526834430485205990846758400000000, by norm_num, R7.Core.Certificates.Terminal075.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal075.polynomial_12, 195907392908704121846124218571386555787060051396269669270695799613991446258690092797093608559363200000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal075.polynomial_13, 511183832486425511647020704800866333129500814962613800869294412799474605637069245570377012295006234180372545793587200000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal075.polynomial_14, 2894697371423545923886122526138401398277552875877473804230291548301837342928794323706342221328434449402000691494397054625222641254400000000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_14⟩
theorem bound_80 : minorBindings polynomial_80 witness_80 := by
 decide +kernel
theorem positive_80 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_80 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_80 ρ hρ u
def polynomial_81 : BiPoly := [[2362215595786272540],[-29363728558050000],[25916293062938059200],[-1141348989572077500],[97600712821853606460],[-1289059337797875000],[153866777116500379800],[644834252466112500],[106575287893403505840],[439380677705580000],[27844781994835587360],[0],[56627326364051520]]
def witness_81 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal075.polynomial_15, 236221559578627254000, by norm_num, R7.Core.Certificates.Terminal075.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal075.polynomial_16, 599952586679363644342657784858322806400000, by norm_num, R7.Core.Certificates.Terminal075.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal075.polynomial_17, 5853109188211713945190022284963938927410256386315958584976000000, by norm_num, R7.Core.Certificates.Terminal075.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal075.polynomial_18, 90057412376110382925051475684455019034565547145845685619398164623652457388480000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal075.polynomial_19, 959783380620811718794783400162154961050083243465342577105525093411609046625380216443347526622320000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_19⟩
 | 5 => ⟨R7.Core.Certificates.Terminal075.polynomial_20, 2672452434395374018446289875896109714506704255196753171898455834709724456383195964911858925979177125008823728587520000000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_20⟩
 | 6 => ⟨R7.Core.Certificates.Terminal075.polynomial_21, 15133383619491082830382426267674841461572817469754547030147378874316381444072796595442459015146164029790433486395330637587410903040000000000000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_21⟩
theorem bound_81 : minorBindings polynomial_81 witness_81 := by
 decide +kernel
theorem positive_81 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_81 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_81 ρ hρ u
def polynomial_82 : BiPoly := [[189860720174079588],[1116144987390000],[2176047239027670972],[-98759706373755000],[8677837210566271860],[-125987872537620000],[14345189930003430780],[66049395757785000],[10287952165762867080],[46778171010480000],[2749453316471186928],[0],[5662732636405152]]
def witness_82 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal075.polynomial_22, 18986072017407958800, by norm_num, R7.Core.Certificates.Terminal075.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal075.polynomial_23, 4048826665710106761995696839122131452800, by norm_num, R7.Core.Certificates.Terminal075.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal075.polynomial_24, 3512031929963603098404605077320509286458388725958227680135296, by norm_num, R7.Core.Certificates.Terminal075.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal075.polynomial_25, 5037915840558844238764041233566655243125703329476290985389791248212173457081088000, by norm_num, R7.Core.Certificates.Terminal075.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal075.polynomial_26, 5182945414983473554800786715621252121680667684183329093708874517208537090723817647078197948578304000000, by norm_num, R7.Core.Certificates.Terminal075.positive_26⟩
 | 5 => ⟨R7.Core.Certificates.Terminal075.polynomial_27, 1424999086147157544524036767597268130844144530287091179577319527627115515926126818888642364820028002550239014921011200000000, by norm_num, R7.Core.Certificates.Terminal075.positive_27⟩
 | 6 => ⟨R7.Core.Certificates.Terminal075.polynomial_28, 806938883197302575576057926381600009343942383890536851683509954008228083183403720790407850192496206786669368468293552173480072970240000000000, by norm_num, R7.Core.Certificates.Terminal075.positive_28⟩
theorem bound_82 : minorBindings polynomial_82 witness_82 := by
 decide +kernel
theorem positive_82 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_82 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_82 ρ hρ u
def polynomial_83 : BiPoly := [[591196562384302332],[-19752851149830000],[6388775531833560444],[-361756468612845000],[23240372073239537460],[-375422399871480000],[35195091506817113340],[165480152736195000],[23353624389235914720],[108035299714680000],[5831643021559906032],[0],[11325465272810304]]
def witness_83 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal075.polynomial_29, 59119656238430233200, by norm_num, R7.Core.Certificates.Terminal075.positive_29⟩
 | 1 => ⟨R7.Core.Certificates.Terminal075.polynomial_30, 37013841458375081146074903644173122998400, by norm_num, R7.Core.Certificates.Terminal075.positive_30⟩
 | 2 => ⟨R7.Core.Certificates.Terminal075.polynomial_31, 85976875676244897696321403192167068831070451834976812685578368, by norm_num, R7.Core.Certificates.Terminal075.positive_31⟩
 | 3 => ⟨R7.Core.Certificates.Terminal076.polynomial_0, 302583358679466363284749683989261185450453139614705303654964766574582551810822912000, by norm_num, R7.Core.Certificates.Terminal076.positive_0⟩
 | 4 => ⟨R7.Core.Certificates.Terminal076.polynomial_1, 706635924595039033255768752166190559971290781549088236223427016487369166641957705548396064417406464000000, by norm_num, R7.Core.Certificates.Terminal076.positive_1⟩
 | 5 => ⟨R7.Core.Certificates.Terminal076.polynomial_2, 412076016745340078084074461887697747154547827643483179584392254962055753434342912905369863817257924433198881426939084800000000, by norm_num, R7.Core.Certificates.Terminal076.positive_2⟩
 | 6 => ⟨R7.Core.Certificates.Terminal076.polynomial_3, 466695261740734636684376966100304627219691727414962907042999887114848349501321901747994881467659679956557358066996319657763751376977920000000000, by norm_num, R7.Core.Certificates.Terminal076.positive_3⟩
theorem bound_83 : minorBindings polynomial_83 witness_83 := by
 decide +kernel
theorem positive_83 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_83 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_83 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL013
