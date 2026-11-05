import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal059
import R7.Certificates.Spectral.Terminal.Terminal060

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL001
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_6 : BiPoly := [[457953557629258257],[673663787960820000],[9456970322072936454],[5051541753405630000],[53999019273372679845],[6366675651647220000],[111935577704744714940],[-311341862815830000],[96855480424276885080],[-1122676104251520000],[31627469360171742624],[0],[79278256909672128]]
def witness_6 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal059.polynomial_2, 45795355762925825700, by norm_num, R7.Core.Certificates.Terminal059.positive_2⟩
 | 1 => ⟨R7.Core.Certificates.Terminal059.polynomial_3, 41307804145174310910408954998574846644400, by norm_num, R7.Core.Certificates.Terminal059.positive_3⟩
 | 2 => ⟨R7.Core.Certificates.Terminal059.polynomial_4, 220214594106060379510965494342020210330396295706124234031942928, by norm_num, R7.Core.Certificates.Terminal059.positive_4⟩
 | 3 => ⟨R7.Core.Certificates.Terminal059.polynomial_5, 2460798796982218336169439261597356243997057368825315899686453623979239764770894432000, by norm_num, R7.Core.Certificates.Terminal059.positive_5⟩
 | 4 => ⟨R7.Core.Certificates.Terminal059.polynomial_6, 23834131605350456239733746032487038184507081220506495302979391795335724105608127546671843609699587456000000, by norm_num, R7.Core.Certificates.Terminal059.positive_6⟩
 | 5 => ⟨R7.Core.Certificates.Terminal059.polynomial_7, 75373572720384091317186227295322292759289307403997435639001617331124268713987931329771160431964077100859418876909092454400000000, by norm_num, R7.Core.Certificates.Terminal059.positive_7⟩
 | 6 => ⟨R7.Core.Certificates.Terminal059.polynomial_8, 597548546232646470128581225304386668390539859061850015977279678746454757596582015436924333721311995037983206562968971892885572194279096320000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_8⟩
theorem bound_6 : minorBindings polynomial_6 witness_6 := by
 decide +kernel
theorem positive_6 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_6 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_6 ρ hρ u
def polynomial_7 : BiPoly := [[659710171728585162],[657422702691255000],[11374497068785481772],[4300768869766132500],[57852575964219686535],[4946896175210145000],[111935170160371228860],[-397367590149090000],[91936880167089191760],[-852030971976600000],[28475229889058279904],[0],[67952791636861824]]
def witness_7 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal059.polynomial_9, 65971017172858516200, by norm_num, R7.Core.Certificates.Terminal059.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal059.polynomial_10, 72457428337797949909650730555024037227200, by norm_num, R7.Core.Certificates.Terminal059.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal059.polynomial_11, 416150870305378615459876338305383576007511103564447560196058496, by norm_num, R7.Core.Certificates.Terminal059.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal059.polynomial_12, 4653758942067474713568023868436365991553975667965444907237919512939549653196339456000, by norm_num, R7.Core.Certificates.Terminal059.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal059.polynomial_13, 42785043541739519695543417924506009197751952217686852932289493114866913307371067669371939448019808256000000, by norm_num, R7.Core.Certificates.Terminal059.positive_13⟩
 | 5 => ⟨R7.Core.Certificates.Terminal059.polynomial_14, 121822948996831401413001390931835010597975586878499543575065387407512026406856168813269771020119147977287519781525808742400000000, by norm_num, R7.Core.Certificates.Terminal059.positive_14⟩
 | 6 => ⟨R7.Core.Certificates.Terminal059.polynomial_15, 827820946976972938563580472506052286503252459474308484506349678622032010402631864583542455281891503353411285676362936307688809716001013760000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_15⟩
theorem bound_7 : minorBindings polynomial_7 witness_7 := by
 decide +kernel
theorem positive_7 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_7 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_7 ρ hρ u
def polynomial_8 : BiPoly := [[713304842051255040],[438772110846525000],[10406269776396610890],[2618001214610895000],[47160816371929608435],[2744276364486450000],[84448718485518406500],[-351809778899700000],[65103544625039244720],[-481146901822080000],[18913436826680776320],[0],[42470494773038640]]
def witness_8 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal059.polynomial_16, 71330484205125504000, by norm_num, R7.Core.Certificates.Terminal059.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal059.polynomial_17, 72262555254972481558015640085845078880000, by norm_num, R7.Core.Certificates.Terminal059.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal059.polynomial_18, 339523207019804762862758145992530624055469705575037724579038000, by norm_num, R7.Core.Certificates.Terminal059.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal059.polynomial_19, 2865869440100248609807357871613198795835199126681382269845032101165441306294700000000, by norm_num, R7.Core.Certificates.Terminal059.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal059.polynomial_20, 18657720841239638537069972314375017567956945053256777136479999950292557250959156900939963423898400000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal059.polynomial_21, 35286503807351209632749613670336110209690354201189611700606136956747036446582190719752357699620286990648380080588800000000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal059.polynomial_22, 149863527550891761819003576774398855888602790934864442939882654714935855961981813016642755138556093382260525398288260256865635123200000000000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_22⟩
theorem bound_8 : minorBindings polynomial_8 witness_8 := by
 decide +kernel
theorem positive_8 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_8 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_8 ρ hρ u
def polynomial_9 : BiPoly := [[566252787184517205],[187233918282675000],[7049099343112480260],[1099329993112747500],[28436813649964043415],[1060216585552800000],[46716737054971824000],[-213125046508687500],[33429669491166390360],[-201034758747420000],[9018907375685740560],[0],[18875775454683840]]
def witness_9 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal059.polynomial_23, 56625278718451720500, by norm_num, R7.Core.Certificates.Terminal059.positive_23⟩
 | 1 => ⟨R7.Core.Certificates.Terminal059.polynomial_24, 39029765721355606291553154797227658340000, by norm_num, R7.Core.Certificates.Terminal059.positive_24⟩
 | 2 => ⟨R7.Core.Certificates.Terminal059.polynomial_25, 110790062944787570543543291013272502748923710924744370375552000, by norm_num, R7.Core.Certificates.Terminal059.positive_25⟩
 | 3 => ⟨R7.Core.Certificates.Terminal059.polynomial_26, 517465344470651456579338070436689156644222093519855922076777332245965844684800000000, by norm_num, R7.Core.Certificates.Terminal059.positive_26⟩
 | 4 => ⟨R7.Core.Certificates.Terminal059.polynomial_27, 1729856963033984310279562583082755536064996047024592575522990587709459968415752158636362045852800000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_27⟩
 | 5 => ⟨R7.Core.Certificates.Terminal059.polynomial_28, 1560089688907456349410208532960873936168251849099583671284586463083167292449027825472351200074041278408827674956800000000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_28⟩
 | 6 => ⟨R7.Core.Certificates.Terminal059.polynomial_29, 2944790265698471237063613655346489118989301509983333080854106110617717794629979209548234592619604399023076199169254866762965811200000000000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_29⟩
theorem bound_9 : minorBindings polynomial_9 witness_9 := by
 decide +kernel
theorem positive_9 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_9 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_9 ρ hρ u
def polynomial_10 : BiPoly := [[313918478542014813],[44612541627390000],[3353021905549064562],[308595671223390000],[12005602784180280945],[281540292883920000],[17923057818433953120],[-84523393076760000],[11774400326629927740],[-60143362727760000],[2924577731533045968],[0],[5662732636405152]]
def witness_10 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal059.polynomial_30, 31391847854201481300, by norm_num, R7.Core.Certificates.Terminal059.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal059.polynomial_31, 10310264546882355484954998433344097678800, by norm_num, R7.Core.Certificates.Terminal059.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal060.polynomial_0, 12367156842658400696756056242490546491997136338319578178471856, by norm_num, R7.Core.Certificates.Terminal060.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal060.polynomial_1, 22163683607898801603532492272669811834474879030518444281805610116959398674339072000, by norm_num, R7.Core.Certificates.Terminal060.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal060.polynomial_2, 26096187467488847287038929602879007683033993165298039004025258930007157957635946261825875097865728000000, by norm_num, R7.Core.Certificates.Terminal060.positive_2⟩
 | 5 => ⟨R7.Core.Certificates.Terminal060.polynomial_3, 7631832447007832452440421650705233082602598896210393154785848839087773796760057777017204714237724969377362803578470400000000, by norm_num, R7.Core.Certificates.Terminal060.positive_3⟩
 | 6 => ⟨R7.Core.Certificates.Terminal060.polynomial_4, 4321702667324704555562441086082065750546714718187077818799425901951284537635289996446586679728109357086813569422943921563539883950080000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_4⟩
theorem bound_10 : minorBindings polynomial_10 witness_10 := by
 decide +kernel
theorem positive_10 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_10 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_10 ρ hρ u
def polynomial_11 : BiPoly := [[109455229693697112],[5285005515270000],[1005310160783223624],[59771991417975000],[3177280333674167040],[52566780553830000],[4264752595257344160],[-19816619397795000],[2545260822754489800],[-11694542752620000],[577910569704134832],[0],[1029587752073664]]
def witness_11 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal060.polynomial_5, 10945522969369711200, by norm_num, R7.Core.Certificates.Terminal060.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal060.polynomial_6, 1078287426498725014167028331535944102400, by norm_num, R7.Core.Certificates.Terminal060.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal060.polynomial_7, 342406399370588829174936983956170994760575570384263033166848, by norm_num, R7.Core.Certificates.Terminal060.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal060.polynomial_8, 146020409046258201303946820614940116886944052987914578557161075107593463840768000, by norm_num, R7.Core.Certificates.Terminal060.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal060.polynomial_9, 37165666490685943273730003506058153494437560251149533308208586397160364690050031002452060016640000000, by norm_num, R7.Core.Certificates.Terminal060.positive_9⟩
 | 5 => ⟨R7.Core.Certificates.Terminal060.polynomial_10, 2147793224278126499814695156369624505294973971996086860243367752750031632346573615557041998957689802983424360448000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_10⟩
 | 6 => ⟨R7.Core.Certificates.Terminal060.polynomial_11, 221134159770356312578906431309423987948957636828401098590782691993616432841517754390906509829282812917824604218266500498404147200000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_11⟩
theorem bound_11 : minorBindings polynomial_11 witness_11 := by
 decide +kernel
theorem positive_11 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_11 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_11 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL001
