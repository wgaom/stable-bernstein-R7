import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch07
import R7.Certificates.Spectral.Terminal.Batches.Batch08
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.CriticalL000
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_0 : BiPoly := r7_rat_grid%[[5094026024832],[331314611760000],[5945898298030368],[8969230680840000],[53064815183059680],[13690399366260000],[121967534352765960],[-12004469730000],[106908874744907880],[-2227531952880000],[35024883012371808],[0],[85798979339472]]
noncomputable def witness_0 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_24, 509402602483200, by norm_num, R7.Core.Certificates.Terminal057.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_25, 22404464663276875454929362124800, by norm_num, R7.Core.Certificates.Terminal057.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_26, 84183700666805821523784030790914113281613194788864, by norm_num, R7.Core.Certificates.Terminal057.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_27, 1016269834356431306376137558289700574667006643474431243773660626944000, by norm_num, R7.Core.Certificates.Terminal057.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_28, 10864826412495286194691976860516710253573533426409652460209980161705489388768591872000000, by norm_num, R7.Core.Certificates.Terminal057.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_29, 38041320835063881549139790926242493025666022789890087008582225844191148061735043543987504323074457600000000, by norm_num, R7.Core.Certificates.Terminal057.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_30, 326390650037387170321393838699465331333015714277219707608708683195643895631395311940798816164240067062152267038720000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_30⟩
theorem bound_0 : minorBindings polynomial_0 witness_0 := by
 decide +kernel
theorem positive_0 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_0 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_0 ρ hρ u
noncomputable def polynomial_1 : BiPoly := r7_rat_grid%[[45846234223488],[3064660158780000],[56486033831288496],[87449999138190000],[530648151830596800],[140326593504165000],[1280659110704042580],[-129048049597500],[1175997622193986680],[-25059734469900000],[402786154642275792],[0],[1029587752073664]]
noncomputable def witness_1 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_31, 4584623422348800, by norm_num, R7.Core.Certificates.Terminal057.positive_31⟩
 | 1 => ⟨R7.Core.Certificates.Terminal058.polynomial_0, 1898430264340535424787460461670400, by norm_num, R7.Core.Certificates.Terminal058.positive_0⟩
 | 2 => ⟨R7.Core.Certificates.Terminal058.polynomial_1, 71117735439362512238460163005579354143143235966902272, by norm_num, R7.Core.Certificates.Terminal058.positive_1⟩
 | 3 => ⟨R7.Core.Certificates.Terminal058.polynomial_2, 9014299982626367300913226050596120302660793036095144146856859018674176000, by norm_num, R7.Core.Certificates.Terminal058.positive_2⟩
 | 4 => ⟨R7.Core.Certificates.Terminal058.polynomial_3, 1060079531570310259378293146047319825764101455702324440727821604206369624265930332397568000000, by norm_num, R7.Core.Certificates.Terminal058.positive_3⟩
 | 5 => ⟨R7.Core.Certificates.Terminal058.polynomial_4, 42684383581430082287086067029085302863620981075096089318928874335209482602172308048395575113599924607385600000000, by norm_num, R7.Core.Certificates.Terminal058.positive_4⟩
 | 6 => ⟨R7.Core.Certificates.Terminal058.polynomial_5, 4394731854025460979927842796459316363322522823528850173578306909826840224048256828660552828803550264905584734744965283840000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_5⟩
theorem bound_1 : minorBindings polynomial_1 witness_1 := by
 decide +kernel
theorem positive_1 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_1 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_1 ρ hρ u
noncomputable def polynomial_2 : BiPoly := r7_rat_grid%[[3472957315436568],[19341944979420000],[301541178406646928],[416080294551990000],[2682392856136172910],[671579283306240000],[6535537784808193620],[-1673214629130000],[6134514193245382380],[-126969321314160000],[2154030305260866192],[0],[5662732636405152]]
noncomputable def witness_2 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal058.polynomial_6, 347295731543656800, by norm_num, R7.Core.Certificates.Terminal058.positive_6⟩
 | 1 => ⟨R7.Core.Certificates.Terminal058.polynomial_7, 9327671397269455318907370289418419200, by norm_num, R7.Core.Certificates.Terminal058.positive_7⟩
 | 2 => ⟨R7.Core.Certificates.Terminal058.polynomial_8, 2361182607668801225154956029029527202573439814162669666304, by norm_num, R7.Core.Certificates.Terminal058.positive_8⟩
 | 3 => ⟨R7.Core.Certificates.Terminal058.polynomial_9, 1532642428568681746675453579364319971952364056571906901971441284881042178048000, by norm_num, R7.Core.Certificates.Terminal058.positive_9⟩
 | 4 => ⟨R7.Core.Certificates.Terminal058.polynomial_10, 940201656596269367807519870423468043417176193257206990318261780955533676506415597827636199424000000, by norm_num, R7.Core.Certificates.Terminal058.positive_10⟩
 | 5 => ⟨R7.Core.Certificates.Terminal058.polynomial_11, 202460516015905508629479483115847761784907748552316227309139928056085127830207873634564372371110084229837147340800000000, by norm_num, R7.Core.Certificates.Terminal058.positive_11⟩
 | 6 => ⟨R7.Core.Certificates.Terminal058.polynomial_12, 114647977162669610179320924936477296101030267235916179791732915582063795189012899440527598948753280211190773205777575426821980160000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_12⟩
theorem bound_2 : minorBindings polynomial_2 witness_2 := by
 decide +kernel
theorem positive_2 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_2 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_2 ρ hρ u
noncomputable def polynomial_3 : BiPoly := r7_rat_grid%[[23986871534789820],[84201281337075000],[1104380609807003820],[1274047712814172500],[8913626845312662405],[1991524901063625000],[21351523582101352500],[-13321467989775000],[20078316280919382120],[-383692378883580000],[7092538810005291120],[0],[18875775454683840]]
noncomputable def witness_3 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal058.polynomial_13, 2398687153478982000, by norm_num, R7.Core.Certificates.Terminal058.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal058.polynomial_14, 241883591519930605209421381781201520000, by norm_num, R7.Core.Certificates.Terminal058.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal058.polynomial_15, 206332517140807399181479423343154513668564447176283549136000, by norm_num, R7.Core.Certificates.Terminal058.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal058.polynomial_16, 438152981072506505609337277223973964393593995763331559642453340981580644000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal058.polynomial_17, 879737321799947098246678615008532521201314094328860982321286523509267002488036186875643528000000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_17⟩
 | 5 => ⟨R7.Core.Certificates.Terminal058.polynomial_18, 623795847716434095908392550823889105504789919182493438369009286321610826867990928181388001640095811094387136000000000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_18⟩
 | 6 => ⟨R7.Core.Certificates.Terminal058.polynomial_19, 1177463035105956521245872423558400861646073816183994892881556359394178290589363720830632741733579262430521669834094544308224000000000000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_19⟩
theorem bound_3 : minorBindings polynomial_3 witness_3 := by
 decide +kernel
theorem positive_3 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_3 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_3 ρ hρ u
noncomputable def polynomial_4 : BiPoly := r7_rat_grid%[[91687783937595990],[243890742134025000],[2969299193300158230],[2751629669975205000],[21410857725311151945],[4061603452833450000],[49497480518437613700],[-59934263677200000],[45878331370255541460],[-771839821672920000],[16023883978160102160],[0],[42470494773038640]]
noncomputable def witness_4 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal058.polynomial_20, 9168778393759599000, by norm_num, R7.Core.Certificates.Terminal058.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal058.polynomial_21, 2519328200990839494854742914009777460000, by norm_num, R7.Core.Certificates.Terminal058.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal058.polynomial_22, 5227942881242989900536402582416429943820632898339185786834000, by norm_num, R7.Core.Certificates.Terminal058.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal058.polynomial_23, 25773099075188924254018858758187048787903629958679939904176905990592583802580000000, by norm_num, R7.Core.Certificates.Terminal058.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal058.polynomial_24, 118242631032551723518922004648573568972869563054351708163158121496557511077881715728201964496680000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_24⟩
 | 5 => ⟨R7.Core.Certificates.Terminal058.polynomial_25, 189432235140655689274870806558379002806442923051392964202422899136644132288744921447748209800181130356164898082880000000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_25⟩
 | 6 => ⟨R7.Core.Certificates.Terminal058.polynomial_26, 804528075238624403270694768602151056600940225884546705107468367585513245395290164234852304070344106207141193123199497244816248320000000000000000, by norm_num, R7.Core.Certificates.Terminal058.positive_26⟩
theorem bound_4 : minorBindings polynomial_4 witness_4 := by
 decide +kernel
theorem positive_4 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_4 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_4 ρ hρ u
noncomputable def polynomial_5 : BiPoly := r7_rat_grid%[[239129251382030733],[484217951946465000],[6046890794958715692],[4341418867054462500],[38797968922821068445],[5954018735762955000],[85387358742362893980],[-167620705410015000],[76941581512343897520],[-1092604422887640000],[26163587610241740576],[0],[67952791636861824]]
noncomputable def witness_5 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal058.polynomial_27, 23912925138203073300, by norm_num, R7.Core.Certificates.Terminal058.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal058.polynomial_28, 13584519433608157025060023024460449912800, by norm_num, R7.Core.Certificates.Terminal058.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal058.polynomial_29, 51620294639692323075870781832455800661923577998969770055518976, by norm_num, R7.Core.Certificates.Terminal058.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal058.polynomial_30, 439568122127310669960178988256812900965097164194575215219402808539818479416616448000, by norm_num, R7.Core.Certificates.Terminal058.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal058.polynomial_31, 3382103023988696264267216572881836312437894756760643405117990674024184675714741017768960740501840896000000, by norm_num, R7.Core.Certificates.Terminal058.positive_31⟩
 | 5 => ⟨R7.Core.Certificates.Terminal059.polynomial_0, 8847483003554467496532681224479457101224174210336961999346587273308346875090962735786303852779114000569398284773939609600000000, by norm_num, R7.Core.Certificates.Terminal059.positive_0⟩
 | 6 => ⟨R7.Core.Certificates.Terminal059.polynomial_1, 60121116905121315036087516510719367242549265427799783880549805506893635281289960206880562019928944874500021414756603076137300103570391040000000000, by norm_num, R7.Core.Certificates.Terminal059.positive_1⟩
theorem bound_5 : minorBindings polynomial_5 witness_5 := by
 decide +kernel
theorem positive_5 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_5 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_5 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL000

namespace R7.Core.SpectralSliceCertificates.CriticalL001
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_6 : BiPoly := r7_rat_grid%[[457953557629258257],[673663787960820000],[9456970322072936454],[5051541753405630000],[53999019273372679845],[6366675651647220000],[111935577704744714940],[-311341862815830000],[96855480424276885080],[-1122676104251520000],[31627469360171742624],[0],[79278256909672128]]
noncomputable def witness_6 : Fin 7 → MinorWitness
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
noncomputable def polynomial_7 : BiPoly := r7_rat_grid%[[659710171728585162],[657422702691255000],[11374497068785481772],[4300768869766132500],[57852575964219686535],[4946896175210145000],[111935170160371228860],[-397367590149090000],[91936880167089191760],[-852030971976600000],[28475229889058279904],[0],[67952791636861824]]
noncomputable def witness_7 : Fin 7 → MinorWitness
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
noncomputable def polynomial_8 : BiPoly := r7_rat_grid%[[713304842051255040],[438772110846525000],[10406269776396610890],[2618001214610895000],[47160816371929608435],[2744276364486450000],[84448718485518406500],[-351809778899700000],[65103544625039244720],[-481146901822080000],[18913436826680776320],[0],[42470494773038640]]
noncomputable def witness_8 : Fin 7 → MinorWitness
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
noncomputable def polynomial_9 : BiPoly := r7_rat_grid%[[566252787184517205],[187233918282675000],[7049099343112480260],[1099329993112747500],[28436813649964043415],[1060216585552800000],[46716737054971824000],[-213125046508687500],[33429669491166390360],[-201034758747420000],[9018907375685740560],[0],[18875775454683840]]
noncomputable def witness_9 : Fin 7 → MinorWitness
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
noncomputable def polynomial_10 : BiPoly := r7_rat_grid%[[313918478542014813],[44612541627390000],[3353021905549064562],[308595671223390000],[12005602784180280945],[281540292883920000],[17923057818433953120],[-84523393076760000],[11774400326629927740],[-60143362727760000],[2924577731533045968],[0],[5662732636405152]]
noncomputable def witness_10 : Fin 7 → MinorWitness
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
noncomputable def polynomial_11 : BiPoly := r7_rat_grid%[[109455229693697112],[5285005515270000],[1005310160783223624],[59771991417975000],[3177280333674167040],[52566780553830000],[4264752595257344160],[-19816619397795000],[2545260822754489800],[-11694542752620000],[577910569704134832],[0],[1029587752073664]]
noncomputable def witness_11 : Fin 7 → MinorWitness
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

namespace R7.Core.SpectralSliceCertificates.CriticalL002
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_12 : BiPoly := r7_rat_grid%[[18242538282282852],[813077771580000],[143615737254746232],[7969598855730000],[397160041709270880],[6184327123980000],[473861399473038240],[-2085959936610000],[254526082275448980],[-1113765976440000],[52537324518557712],[0],[85798979339472]]
noncomputable def witness_12 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal060.polynomial_12, 1824253828228285200, by norm_num, R7.Core.Certificates.Terminal060.positive_12⟩
 | 1 => ⟨R7.Core.Certificates.Terminal060.polynomial_13, 25673519992461646728659241471093907200, by norm_num, R7.Core.Certificates.Terminal060.positive_13⟩
 | 2 => ⟨R7.Core.Certificates.Terminal060.polynomial_14, 1019074323667839212270066057910226744656998672483762881536, by norm_num, R7.Core.Certificates.Terminal060.positive_14⟩
 | 3 => ⟨R7.Core.Certificates.Terminal060.polynomial_15, 48287543750705670746234820714215525475416066501789013772324957892311793664000, by norm_num, R7.Core.Certificates.Terminal060.positive_15⟩
 | 4 => ⟨R7.Core.Certificates.Terminal060.polynomial_16, 1229032847793133588396480868690526576344574081510024239416866547525025043067976423807926272000000, by norm_num, R7.Core.Certificates.Terminal060.positive_16⟩
 | 5 => ⟨R7.Core.Certificates.Terminal060.polynomial_17, 6456860008162633553039866684426005046975354433540253297886105691786555888432667971600822434824036131300966400000000, by norm_num, R7.Core.Certificates.Terminal060.positive_17⟩
 | 6 => ⟨R7.Core.Certificates.Terminal060.polynomial_18, 55399199843820880549294844533741605717479723386769460862278759418136725255612652276736622212347073831931805239830726574080000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_18⟩
theorem bound_12 : minorBindings polynomial_12 witness_12 := by
 decide +kernel
theorem positive_12 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_12 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_12 ρ hρ u
noncomputable def polynomial_13 : BiPoly := r7_rat_grid%[[30564156148992],[2153544976440000],[41621288086212576],[67269230106300000],[424518521464477440],[116368394613210000],[1097707809174893640],[-114042462435000],[1069088747449078800],[-23389085505240000],[385273713136089888],[0],[1029587752073664]]
noncomputable def witness_13 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal060.polynomial_19, 3056415614899200, by norm_num, R7.Core.Certificates.Terminal060.positive_19⟩
 | 1 => ⟨R7.Core.Certificates.Terminal060.polynomial_20, 872381658379079062671033209241600, by norm_num, R7.Core.Certificates.Terminal060.positive_20⟩
 | 2 => ⟨R7.Core.Certificates.Terminal060.polynomial_21, 25539211729968757510751566579448929757926320167780352, by norm_num, R7.Core.Certificates.Terminal060.positive_21⟩
 | 3 => ⟨R7.Core.Certificates.Terminal060.polynomial_22, 2773925599832508961816295101375098469593646729650100986585328448176128000, by norm_num, R7.Core.Certificates.Terminal060.positive_22⟩
 | 4 => ⟨R7.Core.Certificates.Terminal060.polynomial_23, 296557263673799914765962095844721906748713061928968948205508328518650184911221407088640000000, by norm_num, R7.Core.Certificates.Terminal060.positive_23⟩
 | 5 => ⟨R7.Core.Certificates.Terminal060.polynomial_24, 11421778128020188753873053674552946679743623627389800554866690015347088926838737543818455080491110367232000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_24⟩
 | 6 => ⟨R7.Core.Certificates.Terminal060.polynomial_25, 1175972286751244821373831781052361260285536965107498467190159030065575464121851621296469342486366405403158649655577804800000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_25⟩
theorem bound_13 : minorBindings polynomial_13 witness_13 := by
 decide +kernel
theorem positive_13 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_13 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_13 ρ hρ u
noncomputable def polynomial_14 : BiPoly := r7_rat_grid%[[4630609753915424],[26700375154900000],[435748328231034656],[633254494526670000],[4213301590378280040],[1106499367971495000],[11031433532446811400],[-2504054525197500],[11030255584191386640],[-237789035969940000],[4097911312447501536],[0],[11325465272810304]]
noncomputable def witness_14 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal060.polynomial_26, 463060975391542400, by norm_num, R7.Core.Certificates.Terminal060.positive_26⟩
 | 1 => ⟨R7.Core.Certificates.Terminal060.polynomial_27, 17991973414266891173691208041954611200, by norm_num, R7.Core.Certificates.Terminal060.positive_27⟩
 | 2 => ⟨R7.Core.Certificates.Terminal060.polynomial_28, 7145059451008892232609450378446803453363201290516852703232, by norm_num, R7.Core.Certificates.Terminal060.positive_28⟩
 | 3 => ⟨R7.Core.Certificates.Terminal060.polynomial_29, 7826954071801114791872950384959156628166374138136462575856986482334887444480000, by norm_num, R7.Core.Certificates.Terminal060.positive_29⟩
 | 4 => ⟨R7.Core.Certificates.Terminal060.polynomial_30, 8633330273765405417186766428568725822083837105694217881972291601839198306401866501281113374720000000, by norm_num, R7.Core.Certificates.Terminal060.positive_30⟩
 | 5 => ⟨R7.Core.Certificates.Terminal060.polynomial_31, 3536755768393774865114727182071130238142681654941969011063323903574761722254517094401451333543040020241414356992000000000, by norm_num, R7.Core.Certificates.Terminal060.positive_31⟩
 | 6 => ⟨R7.Core.Certificates.Terminal061.polynomial_0, 4005540463335521980199587634460293044041499598048472472582395592036409615343068662036370692410166208792557485683680540095204556800000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_0⟩
theorem bound_14 : minorBindings polynomial_14 witness_14 := by
 decide +kernel
theorem positive_14 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_14 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_14 ρ hρ u
noncomputable def polynomial_15 : BiPoly := r7_rat_grid%[[47973743069579640],[173938762484950000],[2376095248196266840],[2885694951722985000],[20766999716610172530],[4891288284074475000],[53456739581116539000],[-30274001761162500],[53664433750628907120],[-1079796114158580000],[20139307732113789600],[0],[56627326364051520]]
noncomputable def witness_15 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal061.polynomial_1, 4797374306957964000, by norm_num, R7.Core.Certificates.Terminal061.positive_1⟩
 | 1 => ⟨R7.Core.Certificates.Terminal061.polynomial_2, 1041467060132014731237091101247148480000, by norm_num, R7.Core.Certificates.Terminal061.positive_2⟩
 | 2 => ⟨R7.Core.Certificates.Terminal061.polynomial_3, 2067590996756912707397390009951282781843676075192362452608000, by norm_num, R7.Core.Certificates.Terminal061.positive_3⟩
 | 3 => ⟨R7.Core.Certificates.Terminal061.polynomial_4, 10990375377149137856257127841216929396226883586370526310341099051011248371200000000, by norm_num, R7.Core.Certificates.Terminal061.positive_4⟩
 | 4 => ⟨R7.Core.Certificates.Terminal061.polynomial_5, 58979222394709959751101269986741663906418220952505247695201497645053252069095028571434158294400000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_5⟩
 | 5 => ⟨R7.Core.Certificates.Terminal061.polynomial_6, 118748035125264609859187358458906416966104800977559908093061915938925688115586053159033686135064210783926445824000000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_6⟩
 | 6 => ⟨R7.Core.Certificates.Terminal061.polynomial_7, 672438374012821258312498826397549508878128614938564487529402588439763298237374103881496873309897626366716964118580079442485248000000000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_7⟩
theorem bound_15 : minorBindings polynomial_15 witness_15 := by
 decide +kernel
theorem positive_15 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_15 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_15 ρ hρ u
noncomputable def polynomial_16 : BiPoly := r7_rat_grid%[[244500757166922640],[672906206325625000],[8487050893422831960],[8274127306653412500],[66040710368595107340],[13241912227381350000],[163942636129789174200],[-187277062667062500],[162376592547676320000],[-2896905304720440000],[60417923196341368800],[0],[169881979092154560]]
noncomputable def witness_16 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal061.polynomial_8, 24450075716692264000, by norm_num, R7.Core.Certificates.Terminal061.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal061.polynomial_9, 19203878715370817320324427275425329120000, by norm_num, R7.Core.Certificates.Terminal061.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal061.polynomial_10, 122815434117560791036378719973240433583639130125227744153472000, by norm_num, R7.Core.Certificates.Terminal061.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal061.polynomial_11, 2005050186857949251068210039021882340469055980162475649847985684677000894282240000000, by norm_num, R7.Core.Certificates.Terminal061.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal061.polynomial_12, 32557310954235911387803039272196372306067106984580556091366999888272183182300733281178785705680000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal061.polynomial_13, 196662445015838136902433132968472721253304768923322171265932767122354122116876770340576877087632564944455749318400000000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal061.polynomial_14, 3340940537239261012961702708131777879215787193393261923526402219094833054776570533245275122624368881179502823626543713150745190400000000000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_14⟩
theorem bound_16 : minorBindings polynomial_16 witness_16 := by
 decide +kernel
theorem positive_16 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_16 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_16 ρ hρ u
noncomputable def polynomial_17 : BiPoly := r7_rat_grid%[[797097504606769110],[1672825859898000000],[21566915734106747780],[16286577706770547500],[148929283608719728590],[24205098520773450000],[351670135430796003000],[-671129940418987500],[338779779801499559520],[-5118868427718240000],[122937339373425046080],[0],[339763958184309120]]
noncomputable def witness_17 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal061.polynomial_15, 79709750460676911000, by norm_num, R7.Core.Certificates.Terminal061.positive_15⟩
 | 1 => ⟨R7.Core.Certificates.Terminal061.polynomial_16, 161475294300606647174733983331557742840000, by norm_num, R7.Core.Certificates.Terminal061.positive_16⟩
 | 2 => ⟨R7.Core.Certificates.Terminal061.polynomial_17, 2353936768843618394980320453096398468293819389609224006982704000, by norm_num, R7.Core.Certificates.Terminal061.positive_17⟩
 | 3 => ⟨R7.Core.Certificates.Terminal061.polynomial_18, 82544410623094974161830401441530062822402804796163425796738505500800547333211200000000, by norm_num, R7.Core.Certificates.Terminal061.positive_18⟩
 | 4 => ⟨R7.Core.Certificates.Terminal061.polynomial_19, 2796435074850257441598833349098212143570454513842391277145944566304922232735478634757998220094312400000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_19⟩
 | 5 => ⟨R7.Core.Certificates.Terminal061.polynomial_20, 34373221543669862798484985624293269470632182323711138149325137447291747873708538368424924133490893226605714658791539200000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_20⟩
 | 6 => ⟨R7.Core.Certificates.Terminal061.polynomial_21, 1167878180722344064400904910219248722172869814653681691406225873448640531509868556831600629261521979273741757649929271123712245339750400000000000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_21⟩
theorem bound_17 : minorBindings polynomial_17 witness_17 := by
 decide +kernel
theorem positive_17 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_17 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_17 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL002

namespace R7.Core.SpectralSliceCertificates.CriticalL003
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_18 : BiPoly := r7_rat_grid%[[1831814230517033028],[2797295115748985000],[40448528734019860804],[22732404397421310000],[248123981791269310200],[31031697764630205000],[551471422014118291320],[-1524088174834417500],[510291630969671365920],[-6291664000909560000],[177996455468873528256],[0],[475669541458032768]]
noncomputable def witness_18 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal061.polynomial_22, 183181423051703302800, by norm_num, R7.Core.Certificates.Terminal061.positive_22⟩
 | 1 => ⟨R7.Core.Certificates.Terminal061.polynomial_23, 706560917365373157373797193078017718217600, by norm_num, R7.Core.Certificates.Terminal061.positive_23⟩
 | 2 => ⟨R7.Core.Certificates.Terminal061.polynomial_24, 17301192821264004284509995306164792583759222045424770673822150528, by norm_num, R7.Core.Certificates.Terminal061.positive_24⟩
 | 3 => ⟨R7.Core.Certificates.Terminal061.polynomial_25, 952410354947274966304189512032387600786134664382937481513112903797447026902319581696000, by norm_num, R7.Core.Certificates.Terminal061.positive_25⟩
 | 4 => ⟨R7.Core.Certificates.Terminal061.polynomial_26, 48600602867881937088381815389314629993475448264754898589035240961401183373381363797463786665183857020032000000, by norm_num, R7.Core.Certificates.Terminal061.positive_26⟩
 | 5 => ⟨R7.Core.Certificates.Terminal061.polynomial_27, 864979251418104318549725031630867375688026217057978121222425140047891744127909085268952556362282508444214508781554927002419200000000, by norm_num, R7.Core.Certificates.Terminal061.positive_27⟩
 | 6 => ⟨R7.Core.Certificates.Terminal061.polynomial_28, 41144428389276212108426773781014946790217172819121737596554786062038831451593546800686646841370991435528040763834964643650515731254320887234560000000000, by norm_num, R7.Core.Certificates.Terminal061.positive_28⟩
theorem bound_18 : minorBindings polynomial_18 witness_18 := by
 decide +kernel
theorem positive_18 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_18 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_18 ρ hρ u
noncomputable def polynomial_19 : BiPoly := r7_rat_grid%[[3078647468066730756],[3189887244640425000],[56764985756652757584],[22595559095182125000],[309849475499743519470],[28131646412351385000],[642506171629415733000],[-2302125710361592500],[564450345971924096160],[-5543213264741880000],[186822725987991223872],[0],[475669541458032768]]
noncomputable def witness_19 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal061.polynomial_29, 307864746806673075600, by norm_num, R7.Core.Certificates.Terminal061.positive_29⟩
 | 1 => ⟨R7.Core.Certificates.Terminal061.polynomial_30, 1687203469226918651177467804528075024339200, by norm_num, R7.Core.Certificates.Terminal061.positive_30⟩
 | 2 => ⟨R7.Core.Certificates.Terminal061.polynomial_31, 51887484962340250747325716684767307667112595876828341434529835008, by norm_num, R7.Core.Certificates.Terminal061.positive_31⟩
 | 3 => ⟨R7.Core.Certificates.Terminal062.polynomial_0, 3330464843962446843549066920960204744518456238777856071512692355106506543192938086400000, by norm_num, R7.Core.Certificates.Terminal062.positive_0⟩
 | 4 => ⟨R7.Core.Certificates.Terminal062.polynomial_1, 187987515861194261566735390188667414293691927298045693735702395916761189785034757587230455432775230822400000000, by norm_num, R7.Core.Certificates.Terminal062.positive_1⟩
 | 5 => ⟨R7.Core.Certificates.Terminal062.polynomial_2, 3511778176730796729393539477157237845748038533116601105105297096294853814987445321128289341829432646182863854401196907233280000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_2⟩
 | 6 => ⟨R7.Core.Certificates.Terminal062.polynomial_3, 167044591502786443972492614827423315895440071242021806703958589738644407531547147369775045902823757744325147048920992811280307945757846011904000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_3⟩
theorem bound_19 : minorBindings polynomial_19 witness_19 := by
 decide +kernel
theorem positive_19 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_19 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_19 ρ hρ u
noncomputable def polynomial_20 : BiPoly := r7_rat_grid%[[3804292490940026880],[2437344193330650000],[59399104084318403280],[15738137644750732500],[288790334269199178060],[17834836641240600000],[554121461362490627400],[-2355766241480437500],[456972346586939281920],[-3555140996796480000],[141850776200105822400],[0],[339763958184309120]]
noncomputable def witness_20 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal062.polynomial_4, 380429249094002688000, by norm_num, R7.Core.Certificates.Terminal062.positive_4⟩
 | 1 => ⟨R7.Core.Certificates.Terminal062.polynomial_5, 2199669726446161719560059463510175630720000, by norm_num, R7.Core.Certificates.Terminal062.positive_5⟩
 | 2 => ⟨R7.Core.Certificates.Terminal062.polynomial_6, 63279619397885101692211856386885779329991538180613140021499904000, by norm_num, R7.Core.Certificates.Terminal062.positive_6⟩
 | 3 => ⟨R7.Core.Certificates.Terminal062.polynomial_7, 3504710332467405953693814319591620316404564467490742670110746291465681368999976960000000, by norm_num, R7.Core.Certificates.Terminal062.positive_7⟩
 | 4 => ⟨R7.Core.Certificates.Terminal062.polynomial_8, 160154692526601502235663645897785689730748149311051112593299497993425751875110426324297274799894456320000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_8⟩
 | 5 => ⟨R7.Core.Certificates.Terminal062.polynomial_9, 2271696004373029809696228615746095844962760152973111740329999411958252927787034840489617150484624012589092319998487756800000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_9⟩
 | 6 => ⟨R7.Core.Certificates.Terminal062.polynomial_10, 77184042623726020806788668811763401081888282079957266903632843486649924672855421234650291981331917880184045956125328136258909418658201600000000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_10⟩
theorem bound_20 : minorBindings polynomial_20 witness_20 := by
 decide +kernel
theorem positive_20 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_20 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_20 ρ hρ u
noncomputable def polynomial_21 : BiPoly := r7_rat_grid%[[3397516723107103230],[1172434611162375000],[45333110632736143620],[7438516673128087500],[196235990110115805330],[7736397423481350000],[345469563194475297600],[-1620192342469387500],[264434027360373018000],[-1660625070872040000],[76179120551908682400],[0],[169881979092154560]]
noncomputable def witness_21 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal062.polynomial_11, 339751672310710323000, by norm_num, R7.Core.Certificates.Terminal062.positive_11⟩
 | 1 => ⟨R7.Core.Certificates.Terminal062.polynomial_12, 1505959507261189047695521252297007247480000, by norm_num, R7.Core.Certificates.Terminal062.positive_12⟩
 | 2 => ⟨R7.Core.Certificates.Terminal062.polynomial_13, 29498194798186232381842553301274126373839426069949509678219056000, by norm_num, R7.Core.Certificates.Terminal062.positive_13⟩
 | 3 => ⟨R7.Core.Certificates.Terminal062.polynomial_14, 1018847511057627843430116268406548181973808576648015601071391557767295165359106560000000, by norm_num, R7.Core.Certificates.Terminal062.positive_14⟩
 | 4 => ⟨R7.Core.Certificates.Terminal062.polynomial_15, 26941601477889851451776768725954365262714906771584080849834074987785867769651673181425647791761058000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_15⟩
 | 5 => ⟨R7.Core.Certificates.Terminal062.polynomial_16, 205231726557195553096239150888100545367539289250322422629820166497969592442512252438356183927703452486527751550757920000000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_16⟩
 | 6 => ⟨R7.Core.Certificates.Terminal062.polynomial_17, 3486517188003627670890735543969068480288337181220382102800442701436969416870455386089456595059189668668038874623994527147309378411520000000000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_17⟩
theorem bound_21 : minorBindings polynomial_21 witness_21 := by
 decide +kernel
theorem positive_21 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_21 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_21 ρ hρ u
noncomputable def polynomial_22 : BiPoly := r7_rat_grid%[[2092789856946765420],[310797148810500000],[24014364358340821860],[2314097753483745000],[92337995217489052680],[2268865018316250000],[147751385368192315200],[-719338998948075000],[103785777073935216720],[-549643509373140000],[27494533164711869280],[0],[56627326364051520]]
noncomputable def witness_22 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal062.polynomial_18, 209278985694676542000, by norm_num, R7.Core.Certificates.Terminal062.positive_18⟩
 | 1 => ⟨R7.Core.Certificates.Terminal062.polynomial_19, 492277290702292149019360306914995195760000, by norm_num, R7.Core.Certificates.Terminal062.positive_19⟩
 | 2 => ⟨R7.Core.Certificates.Terminal062.polynomial_20, 4541517235183577272390396372200382039160663937591111560696112000, by norm_num, R7.Core.Certificates.Terminal062.positive_20⟩
 | 3 => ⟨R7.Core.Certificates.Terminal062.polynomial_21, 67095211018012882343997211486717036168916711552204110064606520007993180091850240000000, by norm_num, R7.Core.Certificates.Terminal062.positive_21⟩
 | 4 => ⟨R7.Core.Certificates.Terminal062.polynomial_22, 696346986340126782672892950508586299663384424777900080349552519341993376549969247396398474943401280000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_22⟩
 | 5 => ⟨R7.Core.Certificates.Terminal062.polynomial_23, 1914522856009666475776542444361036531578151717417968195632370912090514663824596112541980006807361835157497977234467840000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_23⟩
 | 6 => ⟨R7.Core.Certificates.Terminal062.polynomial_24, 10841431059869539848012958734916273458573606987624129478832784072348890712651405183088061868796158312725232258027336682132925354311680000000000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_24⟩
theorem bound_22 : minorBindings polynomial_22 witness_22 := by
 decide +kernel
theorem positive_22 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_22 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_22 ρ hρ u
noncomputable def polynomial_23 : BiPoly := r7_rat_grid%[[802671684420445488],[40247349693210000],[7946737461429291504],[490130329627395000],[27006882836230419840],[462793813111170000],[38856634756789135680],[-186693414326595000],[24773872008143700720],[-117502310514420000],[5989254995115579168],[0],[11325465272810304]]
noncomputable def witness_23 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal062.polynomial_25, 80267168442044548800, by norm_num, R7.Core.Certificates.Terminal062.positive_25⟩
 | 1 => ⟨R7.Core.Certificates.Terminal062.polynomial_26, 62506437586469223982823905062706632729600, by norm_num, R7.Core.Certificates.Terminal062.positive_26⟩
 | 2 => ⟨R7.Core.Certificates.Terminal062.polynomial_27, 168713800974427806312579097279971903498436556394539231023177728, by norm_num, R7.Core.Certificates.Terminal062.positive_27⟩
 | 3 => ⟨R7.Core.Certificates.Terminal062.polynomial_28, 655531585512093127830239552041522457175224309459148740542291281336533082014613504000, by norm_num, R7.Core.Certificates.Terminal062.positive_28⟩
 | 4 => ⟨R7.Core.Certificates.Terminal062.polynomial_29, 1623990858618393094180684364924474748462949256540071025053858621370352409013233791238397245616652288000000, by norm_num, R7.Core.Certificates.Terminal062.positive_29⟩
 | 5 => ⟨R7.Core.Certificates.Terminal062.polynomial_30, 972626909227998556466428830638449432156689743010441962607232210007592579198150878218928306650341846318182554975233638400000000, by norm_num, R7.Core.Certificates.Terminal062.positive_30⟩
 | 6 => ⟨R7.Core.Certificates.Terminal062.polynomial_31, 1101545228386251745638175489755430177900036787561765950640006413454929130073155967517935219925052370999693618796724798881205736293007360000000000, by norm_num, R7.Core.Certificates.Terminal062.positive_31⟩
theorem bound_23 : minorBindings polynomial_23 witness_23 := by
 decide +kernel
theorem positive_23 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_23 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_23 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL003

namespace R7.Core.SpectralSliceCertificates.CriticalL004
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_24 : BiPoly := r7_rat_grid%[[145940306258262816],[6775648096500000],[1244669722874467344],[71726389701570000],[3706827055953194880],[59781828865140000],[4738613994730382400],[-21554919344970000],[2714944877604789120],[-12251425740840000],[595423011210320736],[0],[1029587752073664]]
noncomputable def witness_24 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_0, 14594030625826281600, by norm_num, R7.Core.Certificates.Terminal063.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_1, 1780030535839712329437414159662510899200, by norm_num, R7.Core.Certificates.Terminal063.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_2, 659452887628827296913494084110095099098215637839920004128768, by norm_num, R7.Core.Certificates.Terminal063.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_3, 312473364237076798597330369963136219869998044098752079584183321459497148088320000, by norm_num, R7.Core.Certificates.Terminal063.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_4, 84834029983825485962072212669156142480353844688167764464254894644684589487957899732402745507840000000, by norm_num, R7.Core.Certificates.Terminal063.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_5, 5051096104983216016885384122016313645859768962956866218088806323985236131084888162172625705905863532630480257024000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_6, 520054668423770932003290030451111500993189336221874518333405043256463677844291575842296233805931545817964434577741406770141593600000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_6⟩
theorem bound_24 : minorBindings polynomial_24 witness_24 := by
 decide +kernel
theorem positive_24 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_24 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_24 ρ hρ u
noncomputable def polynomial_25 : BiPoly := r7_rat_grid%[[4462506895095968],[14855877784480000],[206831243756865488],[263273728942020000],[1878449722323654120],[466473197598840000],[4994040581984896380],[-1876820981805000],[5150267473221453240],[-109149065691120000],[1978905890199007152],[0],[5662732636405152]]
noncomputable def witness_25 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_7, 446250689509596800, by norm_num, R7.Core.Certificates.Terminal063.positive_7⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_8, 8493518581717097837644130546093363200, by norm_num, R7.Core.Certificates.Terminal063.positive_8⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_9, 1521314906401684534894073205000167506176251249426632761344, by norm_num, R7.Core.Certificates.Terminal063.positive_9⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_10, 755130422465087535307988617929007514604646051969848986424861373510110953472000, by norm_num, R7.Core.Certificates.Terminal063.positive_10⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_11, 388912351889275644421975301282293701282143916396992775680461646408728725284546697263722364928000000, by norm_num, R7.Core.Certificates.Terminal063.positive_11⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_12, 76939603741760915112944976783748145851136882710446814477262148302641317799234552739131063834021998772110596505600000000, by norm_num, R7.Core.Certificates.Terminal063.positive_12⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_13, 43568840514054948445448106438543282314960995221563112478653259489993070921288493280373614696568008836326428228020682915703685120000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_13⟩
theorem bound_25 : minorBindings polynomial_25 witness_25 := by
 decide +kernel
theorem positive_25 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_25 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_25 ρ hρ u
noncomputable def polynomial_26 : BiPoly := r7_rat_grid%[[55361079041650960],[161306888533100000],[2084022294914971600],[2352912516976470000],[17972359507574106060],[4089137622584850000],[47576624381796854700],[-28951448238900000],[49576404301148766240],[-990137953055160000],[19351247864335423920],[0],[56627326364051520]]
noncomputable def witness_26 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_14, 5536107904165096000, by norm_num, R7.Core.Certificates.Terminal063.positive_14⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_15, 1065612704614260718020198213024812800000, by norm_num, R7.Core.Certificates.Terminal063.positive_15⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_16, 1841602838082346188671031707948644429810794385263774592000000, by norm_num, R7.Core.Certificates.Terminal063.positive_16⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_17, 8717179249836856078216248580798002003756145170157377727090627987537578240000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_17⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_18, 43216636426533742598570935785545044468949620991291019207078556649134224200450257560547061760000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_18⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_19, 83608219113721027988879530235460629478615911560650436200378087708388334496899143563084272730870977776642129920000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_19⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_20, 473450991046981097782459862868442190475619331457905112260137478333016655708504371553214317824298649826479945978698181341347840000000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_20⟩
theorem bound_26 : minorBindings polynomial_26 witness_26 := by
 decide +kernel
theorem positive_26 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_26 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_26 ρ hρ u
noncomputable def polynomial_27 : BiPoly := r7_rat_grid%[[355586004721084940],[848531412531150000],[10664095510191059700],[9947411646553380000],[83935498079834693085],[16465287019640850000],[215968058656698555900],[-228375133081425000],[223003012585217841360],[-3969461940032160000],[86686585455620224800],[0],[254822968638231840]]
noncomputable def witness_27 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_21, 35558600472108494000, by norm_num, R7.Core.Certificates.Terminal063.positive_21⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_22, 35361616645912137232290218222396996400000, by norm_num, R7.Core.Certificates.Terminal063.positive_22⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_23, 288344305027427208325572466854351489975364465618323064446000000, by norm_num, R7.Core.Certificates.Terminal063.positive_23⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_24, 6203349140629227057196629695593727300610086708546214656357114604187583353140000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_24⟩
 | 4 => ⟨R7.Core.Certificates.Terminal063.polynomial_25, 138336517051185719926823616053672759265328928847216821198365449502939688647023740269144490912040000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_25⟩
 | 5 => ⟨R7.Core.Certificates.Terminal063.polynomial_26, 1198947671035692067919156390938996786251299875029724789955095910266514279119730420526730468429961071149137222659200000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_26⟩
 | 6 => ⟨R7.Core.Certificates.Terminal063.polynomial_27, 30551940477520926483004146977669162265177307465635738083152543396542921980554243186736870789810193632479828328517896053587090892800000000000000000000, by norm_num, R7.Core.Certificates.Terminal063.positive_27⟩
theorem bound_27 : minorBindings polynomial_27 witness_27 := by
 decide +kernel
theorem positive_27 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_27 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_27 ρ hρ u
noncomputable def polynomial_28 : BiPoly := r7_rat_grid%[[1402443455171490580],[2672186246729625000],[35081108689767730880],[25747058019712740000],[248564183566323641400],[39817900756778400000],[611483094295925245200],[-1042830083405137500],[616022736130022640480],[-9288808243509600000],[234316467352767395520],[0],[679527916368618240]]
noncomputable def witness_28 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal063.polynomial_28, 140244345517149058000, by norm_num, R7.Core.Certificates.Terminal063.positive_28⟩
 | 1 => ⟨R7.Core.Certificates.Terminal063.polynomial_29, 464301410221792300587245615010609581920000, by norm_num, R7.Core.Certificates.Terminal063.positive_29⟩
 | 2 => ⟨R7.Core.Certificates.Terminal063.polynomial_30, 11316283335122571166017153994486617346183002795465449741087744000, by norm_num, R7.Core.Certificates.Terminal063.positive_30⟩
 | 3 => ⟨R7.Core.Certificates.Terminal063.polynomial_31, 690131260624471821830272997958185325172477491805738107031774642632472315791482880000000, by norm_num, R7.Core.Certificates.Terminal063.positive_31⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_0, 42513623979882826413644711771848557533881330103162368176773598896111120311894494379369615194831498240000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_0⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_1, 996015353840886331747412657804713681207690176831868049463126012826264953256548423520670236739322924234505212386426388480000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_1⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_2, 67682023806664951135100872139884560124144588990693060548771491464655154949649497643119757724766280824333177738706236911193150289105387520000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_2⟩
theorem bound_28 : minorBindings polynomial_28 witness_28 := by
 decide +kernel
theorem positive_28 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_28 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_28 ρ hρ u
noncomputable def polynomial_29 : BiPoly := r7_rat_grid%[[3783954436662442855],[5414723055778225000],[80621568388176022390],[44382349396965990000],[512000711312030462685],[63320277294598950000],[1189731360645749754900],[-2942991064334475000],[1153930040936907529680],[-14127007645164960000],[422925462374389581600],[0],[1189173853645081920]]
noncomputable def witness_29 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal064.polynomial_3, 378395443666244285500, by norm_num, R7.Core.Certificates.Terminal064.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal064.polynomial_4, 2916371681225666778917944606258277629810000, by norm_num, R7.Core.Certificates.Terminal064.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal064.polynomial_5, 147500555311507221980511601023713739316054218879013957872548938000, by norm_num, R7.Core.Certificates.Terminal064.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal064.polynomial_6, 17519370965779618552222445459711585253826357121635436866641992883736644402675529620000000, by norm_num, R7.Core.Certificates.Terminal064.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_7, 2021609651744896036441315977519413726405620069858928744747684937539367651118501213055313929362146287160000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_7⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_8, 85490278715607184673947251621821424072035305171585738713345731265902013249268897942027935256022259106611800618874105225600000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_8⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_9, 10166280418943072016839941858514634879661685154044819199347306354439865856490224603748894968276596048416442318444492927093468227401208115200000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_9⟩
theorem bound_29 : minorBindings polynomial_29 witness_29 := by
 decide +kernel
theorem positive_29 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_29 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_29 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL004

namespace R7.Core.SpectralSliceCertificates.CriticalL005
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_30 : BiPoly := r7_rat_grid%[[7308172172002734252],[7242187540418145000],[133917456722793339492],[52285002579260482500],[761324390015306392320],[68258434777118820000],[1654749169084390259340],[-5372850590236552500],[1526511952970230514400],[-14735123868301200000],[531782798776841160864],[0],[1427008624374098304]]
noncomputable def witness_30 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal064.polynomial_10, 730817217200273425200, by norm_num, R7.Core.Certificates.Terminal064.positive_10⟩
 | 1 => ⟨R7.Core.Certificates.Terminal064.polynomial_11, 9460056738629138353846366218926745763843200, by norm_num, R7.Core.Certificates.Terminal064.positive_11⟩
 | 2 => ⟨R7.Core.Certificates.Terminal064.polynomial_12, 715240747501020167274107847557412468848935534000924282595304418176, by norm_num, R7.Core.Certificates.Terminal064.positive_12⟩
 | 3 => ⟨R7.Core.Certificates.Terminal064.polynomial_13, 118244212192201648955470136913853452528481007922277953503004170141572175806812044976384000, by norm_num, R7.Core.Certificates.Terminal064.positive_13⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_14, 18050068710021754080445797018204772404016160534266555948777472842288737120234740526918057931012263123192960000000, by norm_num, R7.Core.Certificates.Terminal064.positive_14⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_15, 959807421568974367059802108458210360623545191455512663693192251446338950150600125242883968781590560700738547980633546467231744000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_15⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_16, 136965346831719236120484546223979496356578955644524432202225961184204775270402942575755556951822698334693136631815719813942206667345684300536217600000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_16⟩
theorem bound_30 : minorBindings polynomial_30 witness_30 := by
 decide +kernel
theorem positive_30 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_30 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_30 ρ hρ u
noncomputable def polynomial_31 : BiPoly := r7_rat_grid%[[10224468613004980370],[6308630406199200000],[161944282032500516400],[41809962294057765000],[823584431115063598395],[49816418528929050000],[1659655293029056584000],[-6485930661568050000],[1439264806951322514240],[-10852535674431360000],[470734427686277099520],[0],[1189173853645081920]]
noncomputable def witness_31 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal064.polynomial_17, 1022446861300498037000, by norm_num, R7.Core.Certificates.Terminal064.positive_17⟩
 | 1 => ⟨R7.Core.Certificates.Terminal064.polynomial_18, 16127286397224840891189104784809258066400000, by norm_num, R7.Core.Certificates.Terminal064.positive_18⟩
 | 2 => ⟨R7.Core.Certificates.Terminal064.polynomial_19, 1323547275090721186543040033419292015960341455989860902450288000000, by norm_num, R7.Core.Certificates.Terminal064.positive_19⟩
 | 3 => ⟨R7.Core.Certificates.Terminal064.polynomial_20, 219563167336796838481337870978441440832876294134346420007972820501084344909619200000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_20⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_21, 31600814769922295337155532224905873098574636900346530899912354786413712125063616647441665800197740800000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_21⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_22, 1487494496494812615638729045934631596150316370143655433003548278591225050205738631957957491475772385828839439887276441600000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_22⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_23, 176888956267258711844042246771355320064089202959001558742891279166420479530959900221520751587007148208665847938256294898781035531809587200000000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_23⟩
theorem bound_31 : minorBindings polynomial_31 witness_31 := by
 decide +kernel
theorem positive_31 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_31 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_31 ρ hρ u
noncomputable def polynomial_32 : BiPoly := r7_rat_grid%[[10222960422023587380],[3345866257878675000],[140374309180349855100],[22008114707977635000],[637697545500560911920],[24142546257546600000],[1180908100372306159800],[-5158289429725162500],[951527592552620230560],[-5706936863278560000],[288955284852067416000],[0],[679527916368618240]]
noncomputable def witness_32 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal064.polynomial_24, 1022296042202358738000, by norm_num, R7.Core.Certificates.Terminal064.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal064.polynomial_25, 14035414816253237511250093127709786152400000, by norm_num, R7.Core.Certificates.Terminal064.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal064.polynomial_26, 893577675409855058965812809413585171743665047833566290702002000000, by norm_num, R7.Core.Certificates.Terminal064.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal064.polynomial_27, 105502859726518021386347534867166340396729821640960819339015031212854921079191960000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal064.polynomial_28, 10038828771624133167859292792576672670528561186111912534570691957156292456792678306500140567894048510000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal064.polynomial_29, 290068672388125811238858582488796669843874791395711410456846699969187615066634259978004568342438266649883087808795016000000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal064.polynomial_30, 19710976055171447915179848421476636469266333051777270646981592963205975077169017271271585380101113238959666746348608372751013131869184000000000000000000000, by norm_num, R7.Core.Certificates.Terminal064.positive_30⟩
theorem bound_32 : minorBindings polynomial_32 witness_32 := by
 decide +kernel
theorem positive_32 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_32 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_32 ρ hρ u
noncomputable def polynomial_33 : BiPoly := r7_rat_grid%[[6989714323388164335],[909119173411875000],[83363619356948939010],[7358122624031880000],[337266282600534932175],[7674855814778850000],[568379813482472261400],[-2605647474762750000],[420544476489383885880],[-2105017695471600000],[117420920298976486320],[0],[254822968638231840]]
noncomputable def witness_33 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal064.polynomial_31, 698971432338816433500, by norm_num, R7.Core.Certificates.Terminal064.positive_31⟩
 | 1 => ⟨R7.Core.Certificates.Terminal065.polynomial_0, 5708275021655036630877768819604705141830000, by norm_num, R7.Core.Certificates.Terminal065.positive_0⟩
 | 2 => ⟨R7.Core.Certificates.Terminal065.polynomial_1, 192372273886131060065133927613254950306760201591208370757478302000, by norm_num, R7.Core.Certificates.Terminal065.positive_1⟩
 | 3 => ⟨R7.Core.Certificates.Terminal065.polynomial_2, 10933211122874472646368513088789496499936643717478502787742538300146145895237214280000000, by norm_num, R7.Core.Certificates.Terminal065.positive_2⟩
 | 4 => ⟨R7.Core.Certificates.Terminal065.polynomial_3, 459786889571519636987935000915594548871105956711494108383097852782190197137716385629298555826075136640000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_3⟩
 | 5 => ⟨R7.Core.Certificates.Terminal065.polynomial_4, 5398738856123368990544659956249842938452491615104299515990820328976212982151942074166597742817142939524665024702109076480000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_4⟩
 | 6 => ⟨R7.Core.Certificates.Terminal065.polynomial_5, 137572266221992889415286724443659605316196199867553170831833316898638567518398263413392971285552918906795157263622043482764512040253112320000000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_5⟩
theorem bound_33 : minorBindings polynomial_33 witness_33 := by
 decide +kernel
theorem positive_33 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_33 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_33 ρ hρ u
noncomputable def polynomial_34 : BiPoly := r7_rat_grid%[[2955982811921511660],[89262327768075000],[30625275291663314880],[1634153148967792500],[109727932284773978220],[1676721087036450000],[166412411982588614400],[-759238397929687500],[111765867689949626880],[-500080923421560000],[28457717447552094000],[0],[56627326364051520]]
noncomputable def witness_34 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal065.polynomial_6, 295598281192151166000, by norm_num, R7.Core.Certificates.Terminal065.positive_6⟩
 | 1 => ⟨R7.Core.Certificates.Terminal065.polynomial_7, 887152396842812484701046623720418207840000, by norm_num, R7.Core.Certificates.Terminal065.positive_7⟩
 | 2 => ⟨R7.Core.Certificates.Terminal065.polynomial_8, 9729773772953776206442324146274601112218759193719152872265344000, by norm_num, R7.Core.Certificates.Terminal065.positive_8⟩
 | 3 => ⟨R7.Core.Certificates.Terminal065.polynomial_9, 161909276823781936333356049231960720827247775164507212146499123994177855009935360000000, by norm_num, R7.Core.Certificates.Terminal065.positive_9⟩
 | 4 => ⟨R7.Core.Certificates.Terminal065.polynomial_10, 1809579059477606938822913584718402340891685214292475907225870142800675242637911102360884626241847680000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_10⟩
 | 5 => ⟨R7.Core.Certificates.Terminal065.polynomial_11, 5149547731305783124287854114044804057641400671207341884280048941989650011030812103602384819849737181068053871064192000000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_11⟩
 | 6 => ⟨R7.Core.Certificates.Terminal065.polynomial_12, 29160512000791366555876876394379850573444665219159649175663365486581892280626930381922193272192800765788470711065420251339511517184000000000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_12⟩
theorem bound_34 : minorBindings polynomial_34 witness_34 := by
 decide +kernel
theorem positive_34 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_34 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_34 ρ hρ u
noncomputable def polynomial_35 : BiPoly := r7_rat_grid%[[591196562384302332],[16771565987370000],[5287721546213839332],[266121282344085000],[16621038044751689460],[241428645518580000],[22400833721045080860],[-97338794806935000],[13511949207918554160],[-57915830774880000],[3117214588101090912],[0],[5662732636405152]]
noncomputable def witness_35 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal065.polynomial_13, 59119656238430233200, by norm_num, R7.Core.Certificates.Terminal065.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal065.polynomial_14, 30634908235912718814931429145367037795200, by norm_num, R7.Core.Certificates.Terminal065.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal065.polynomial_15, 50893559537213222395860348441575907000886974782181837463767936, by norm_num, R7.Core.Certificates.Terminal065.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal065.polynomial_16, 114001352363710170680056801088420506175898017008053063812614522190458473339530496000, by norm_num, R7.Core.Certificates.Terminal065.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal065.polynomial_17, 154036842756289664168116636359697518803027436867738374116366824651840790777083743345468155730766336000000, by norm_num, R7.Core.Certificates.Terminal065.positive_17⟩
 | 5 => ⟨R7.Core.Certificates.Terminal065.polynomial_18, 48015633363769118481467203438559930868639979293509953310285135493576310470310741405688656818368220004894618480513843200000000, by norm_num, R7.Core.Certificates.Terminal065.positive_18⟩
 | 6 => ⟨R7.Core.Certificates.Terminal065.polynomial_19, 27189969410667947708255287996618814177929087279101426049171201582872518487219057375901701052237521437422035688179753440504381980016640000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_19⟩
theorem bound_35 : minorBindings polynomial_35 witness_35 := by
 decide +kernel
theorem positive_35 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_35 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_35 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL005

namespace R7.Core.SpectralSliceCertificates.CriticalL006
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_36 : BiPoly := r7_rat_grid%[[22032363044114080],[58018333073800000],[699910717420429440],[691029248177580000],[5720073930637223640],[1171181089727100000],[15070947647914915200],[-13044895553250000],[15883377956694333360],[-296261749733040000],[6304478942226925440],[0],[18875775454683840]]
noncomputable def witness_36 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal065.polynomial_20, 2203236304411408000, by norm_num, R7.Core.Certificates.Terminal065.positive_20⟩
 | 1 => ⟨R7.Core.Certificates.Terminal065.polynomial_21, 142707415410141788316651491915048960000, by norm_num, R7.Core.Certificates.Terminal065.positive_21⟩
 | 2 => ⟨R7.Core.Certificates.Terminal065.polynomial_22, 79106169568258869030163224152191620756225806215121338368000, by norm_num, R7.Core.Certificates.Terminal065.positive_22⟩
 | 3 => ⟨R7.Core.Certificates.Terminal065.polynomial_23, 118731127049926545271174637011780390156993030833692595952774156241322639360000000, by norm_num, R7.Core.Certificates.Terminal065.positive_23⟩
 | 4 => ⟨R7.Core.Certificates.Terminal065.polynomial_24, 188585102962224006465225407362734439982638118782811079045312476004291666732456541439089704960000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_24⟩
 | 5 => ⟨R7.Core.Certificates.Terminal065.polynomial_25, 118867028162693828415220519968760736621833167027789021657133062345452009688261278998989421267499975348311818240000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_25⟩
 | 6 => ⟨R7.Core.Certificates.Terminal065.polynomial_26, 224370733256458891345608375844691515950079471679769654382666990680214858636296634437299080179741052846483650221489103474524160000000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_26⟩
theorem bound_36 : minorBindings polynomial_36 witness_36 := by
 decide +kernel
theorem positive_36 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_36 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_36 ρ hρ u
noncomputable def polynomial_37 : BiPoly := r7_rat_grid%[[252308562175904240],[548352316253500000],[6698587774347507600],[5701530725547930000],[51658891970851887300],[9336027886107750000],[134230252006384315200],[-143392649367825000],[141320484260979809760],[-2355615040170600000],[56214937234856751840],[0],[169881979092154560]]
noncomputable def witness_37 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal065.polynomial_27, 25230856217590424000, by norm_num, R7.Core.Certificates.Terminal065.positive_27⟩
 | 1 => ⟨R7.Core.Certificates.Terminal065.polynomial_28, 15811362632704712998436962373667795200000, by norm_num, R7.Core.Certificates.Terminal065.positive_28⟩
 | 2 => ⟨R7.Core.Certificates.Terminal065.polynomial_29, 79704528036015761014639797265197298295147833680334676352000000, by norm_num, R7.Core.Certificates.Terminal065.positive_29⟩
 | 3 => ⟨R7.Core.Certificates.Terminal065.polynomial_30, 1066430536515260097297413376632285531021939540735366747281038058932115415040000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_30⟩
 | 4 => ⟨R7.Core.Certificates.Terminal065.polynomial_31, 15070843888001259775772335062322726397545659658902127027326147987466018086854397413716064279040000000000000, by norm_num, R7.Core.Certificates.Terminal065.positive_31⟩
 | 5 => ⟨R7.Core.Certificates.Terminal066.polynomial_0, 84705860473787865614920756390375938224104794180529628301399693620308640939223685294277099651617087124462579343360000000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_0⟩
 | 6 => ⟨R7.Core.Certificates.Terminal066.polynomial_1, 1438999921799099153823210231285611267951495076040561522557345688529074266327008825141713652306949794739004824273103154529242972160000000000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_1⟩
theorem bound_37 : minorBindings polynomial_37 witness_37 := by
 decide +kernel
theorem positive_37 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_37 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_37 ρ hρ u
noncomputable def polynomial_38 : BiPoly := r7_rat_grid%[[1375997151476530520],[2420489023866800000],[31628459829512558760],[21661456431675075000],[223936538956708809240],[33495304956770700000],[561511879873070983200],[-811200455779725000],[580101354215733592800],[-8159449543399440000],[226961241920169315840],[0],[679527916368618240]]
noncomputable def witness_38 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal066.polynomial_2, 137599715147653052000, by norm_num, R7.Core.Certificates.Terminal066.positive_2⟩
 | 1 => ⟨R7.Core.Certificates.Terminal066.polynomial_3, 411855654397142563471940516977846880960000, by norm_num, R7.Core.Certificates.Terminal066.positive_3⟩
 | 2 => ⟨R7.Core.Certificates.Terminal066.polynomial_4, 9066732988524625474173597528369360888515209459530694806625152000, by norm_num, R7.Core.Certificates.Terminal066.positive_4⟩
 | 3 => ⟨R7.Core.Certificates.Terminal066.polynomial_5, 507952639817717197363865145865850130004606812354638428387172089621620333048944640000000, by norm_num, R7.Core.Certificates.Terminal066.positive_5⟩
 | 4 => ⟨R7.Core.Certificates.Terminal066.polynomial_6, 29466386507748942590259936913278056272556151710926989116666300631424362993367881886821522495750259200000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_6⟩
 | 5 => ⟨R7.Core.Certificates.Terminal066.polynomial_7, 668688223249142731317060694329821406690208899935439414405577428943744465897412682615093851964751387363785531758906572800000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_7⟩
 | 6 => ⟨R7.Core.Certificates.Terminal066.polynomial_8, 45439231504472338496125626399034435225742285782625070974182019963159535618877005403824843898927450885948911471467846030791852998996787200000000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_8⟩
theorem bound_38 : minorBindings polynomial_38 witness_38 := by
 decide +kernel
theorem positive_38 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_38 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_38 ρ hρ u
noncomputable def polynomial_39 : BiPoly := r7_rat_grid%[[4652373695363282160],[6257226748602825000],[93946366524684363120],[48830351839678680000],[603996437014886493960],[70168232124467100000],[1439652980857213087200],[-2834139272432737500],[1437939668565024478560],[-16232025340636560000],[544286682012257896320],[0],[1585565138193442560]]
noncomputable def witness_39 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal066.polynomial_9, 465237369536328216000, by norm_num, R7.Core.Certificates.Terminal066.positive_9⟩
 | 1 => ⟨R7.Core.Certificates.Terminal066.polynomial_10, 4185439106606534851170316545142525304160000, by norm_num, R7.Core.Certificates.Terminal066.positive_10⟩
 | 2 => ⟨R7.Core.Certificates.Terminal066.polynomial_11, 250088012115382872995906748174335781889017801711480289831673856000, by norm_num, R7.Core.Certificates.Terminal066.positive_11⟩
 | 3 => ⟨R7.Core.Certificates.Terminal066.polynomial_12, 35952476842799947972344696310242356869379073000271115956035408437355515444528824320000000, by norm_num, R7.Core.Certificates.Terminal066.positive_12⟩
 | 4 => ⟨R7.Core.Certificates.Terminal066.polynomial_13, 5169744241559503491132024622917730096035308470743649073949332094189710477252025024987245589516184657920000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_13⟩
 | 5 => ⟨R7.Core.Certificates.Terminal066.polynomial_14, 281358612234183428987670185414211154563830625097547760517162486158671746840619297406752879147452449225281166249752922685440000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_14⟩
 | 6 => ⟨R7.Core.Certificates.Terminal066.polynomial_15, 44611240688900826712877623984772242554933910101080265789125557725130429343454562920672247983309140323397474470999884084278080892247358832640000000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_15⟩
theorem bound_39 : minorBindings polynomial_39 witness_39 := by
 decide +kernel
theorem positive_39 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_39 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_39 ρ hρ u
noncomputable def polynomial_40 : BiPoly := r7_rat_grid%[[10697850666332539980],[10130097728698650000],[190734526478254495560],[70476951975701370000],[1107647295438874609380],[93131873585367750000],[2480716016516485627200],[-6356062627221037500],[2364137965916839607040],[-20629173415621680000],[853206150181377242880],[0],[2378347707290163840]]
noncomputable def witness_40 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal066.polynomial_16, 1069785066633253998000, by norm_num, R7.Core.Certificates.Terminal066.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal066.polynomial_17, 19739857715562096316701840701258388390240000, by norm_num, R7.Core.Certificates.Terminal066.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal066.polynomial_18, 2173196798525772186909921975463970557199396872153422583130101632000, by norm_num, R7.Core.Certificates.Terminal066.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal066.polynomial_19, 538680374110744158607471252732494146733730974971569831344395913032143304260326359040000000, by norm_num, R7.Core.Certificates.Terminal066.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal066.polynomial_20, 127351252902615019140295390228200113906149541650218902694019819744079182680228671734472124292019205164160000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal066.polynomial_21, 10865114115166371677972544742884981958988069141538781806274840901316297300222387637849101203706050243966741620918733619118080000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal066.polynomial_22, 2584101924525193723751062084314315840406296132668692081682148250726627289702920410775771711081204904558106028839585991738690100510295950622720000000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_22⟩
theorem bound_40 : minorBindings polynomial_40 witness_40 := by
 decide +kernel
theorem positive_40 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_40 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_40 ρ hρ u
noncomputable def polynomial_41 : BiPoly := r7_rat_grid%[[17304373531004837560],[10282948953284475000],[272309280928469291280],[65906185292507422500],[1423832905386996421380],[79746272246157750000],[2966352441487384980600],[-9266831542306800000],[2664013922934405924960],[-17682148641961440000],[904692728209563800640],[0],[2378347707290163840]]
noncomputable def witness_41 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal066.polynomial_23, 1730437353100483756000, by norm_num, R7.Core.Certificates.Terminal066.positive_23⟩
 | 1 => ⟨R7.Core.Certificates.Terminal066.polynomial_24, 45914639230886895624358966778666237372640000, by norm_num, R7.Core.Certificates.Terminal066.positive_24⟩
 | 2 => ⟨R7.Core.Certificates.Terminal066.polynomial_25, 6517630370211022281961086128056592969483742717334277181774415104000, by norm_num, R7.Core.Certificates.Terminal066.positive_25⟩
 | 3 => ⟨R7.Core.Certificates.Terminal066.polynomial_26, 1932628894448691937545182097142159720838662472467310142910071935189426009303938698240000000, by norm_num, R7.Core.Certificates.Terminal066.positive_26⟩
 | 4 => ⟨R7.Core.Certificates.Terminal066.polynomial_27, 514853629027469946260563768857445125419894497500126544180367201474630415104044711896518830879186152407040000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_27⟩
 | 5 => ⟨R7.Core.Certificates.Terminal066.polynomial_28, 46576922795794565151241813101053320454908248934881786605079084362274994469195646021845701857914697297566890938705202509250560000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_28⟩
 | 6 => ⟨R7.Core.Certificates.Terminal066.polynomial_29, 11077611754400897204432936126682722924663117025760801384687436399406660102149081038160096728255653285785497470348822766848262185252769801175040000000000000000, by norm_num, R7.Core.Certificates.Terminal066.positive_29⟩
theorem bound_41 : minorBindings polynomial_41 witness_41 := by
 decide +kernel
theorem positive_41 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_41 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_41 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL006

namespace R7.Core.SpectralSliceCertificates.CriticalL007
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_42 : BiPoly := r7_rat_grid%[[19639436932673384680],[6108443720762625000],[272216048301077086200],[38817054383100922500],[1277463241526252637000],[43373254207188150000],[2451767282991185076000],[-8731686531506400000],[2049665376571586796960],[-10525088477358000000],[647259838068631011840],[0],[1585565138193442560]]
noncomputable def witness_42 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal066.polynomial_30, 1963943693267338468000, by norm_num, R7.Core.Certificates.Terminal066.positive_30⟩
 | 1 => ⟨R7.Core.Certificates.Terminal066.polynomial_31, 52299182432447327071517587190085407776800000, by norm_num, R7.Core.Certificates.Terminal066.positive_31⟩
 | 2 => ⟨R7.Core.Certificates.Terminal067.polynomial_0, 6671976221821210567340324514878634961558654666103081487055056000000, by norm_num, R7.Core.Certificates.Terminal067.positive_0⟩
 | 3 => ⟨R7.Core.Certificates.Terminal067.polynomial_1, 1635567333177885291726076576887057166825975065288511479499161838654900824754425600000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_1⟩
 | 4 => ⟨R7.Core.Certificates.Terminal067.polynomial_2, 335235301668763145711087926518965529012249680543828816511359160272505309626070220185318114994462617600000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_2⟩
 | 5 => ⟨R7.Core.Certificates.Terminal067.polynomial_3, 21697981747201892864120357729416236630195924221583071486608693218210970897872896515385872543064398695774784928294299238400000000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_3⟩
 | 6 => ⟨R7.Core.Certificates.Terminal067.polynomial_4, 3440356342752096350897221724433239603929131967474277820311761441556493351918519190044755177854563683351725441032260625652565657728214630400000000000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_4⟩
theorem bound_42 : minorBindings polynomial_42 witness_42 := by
 decide +kernel
theorem positive_42 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_42 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_42 ρ hρ u
noncomputable def polynomial_43 : BiPoly := r7_rat_grid%[[15060130078194628640],[1700041219787850000],[183356648536691264520],[13706520848770087500],[768908732875129222680],[14729429636294850000],[1345409188836572077200],[-5132439155389837500],[1034153708465320509600],[-4350369903974640000],[300513496246150112640],[0],[679527916368618240]]
noncomputable def witness_43 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal067.polynomial_5, 1506013007819462864000, by norm_num, R7.Core.Certificates.Terminal067.positive_5⟩
 | 1 => ⟨R7.Core.Certificates.Terminal067.polynomial_6, 27054249430738531092188174826983146957440000, by norm_num, R7.Core.Certificates.Terminal067.positive_6⟩
 | 2 => ⟨R7.Core.Certificates.Terminal067.polynomial_7, 2078934785561541716304015728460199126111143479916200285554694016000, by norm_num, R7.Core.Certificates.Terminal067.positive_7⟩
 | 3 => ⟨R7.Core.Certificates.Terminal067.polynomial_8, 279687122387711513337529420916324805973546466223299249174244888536431497517553003520000000, by norm_num, R7.Core.Certificates.Terminal067.positive_8⟩
 | 4 => ⟨R7.Core.Certificates.Terminal067.polynomial_9, 28923810574829342213645306178125562887375315601632599658782196499343919945651760812296636721016549379200000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_9⟩
 | 5 => ⟨R7.Core.Certificates.Terminal067.polynomial_10, 869186310861106342947471987494473049924219333230460052858017708967317092492968435071854181896772319868920688231879727308800000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_10⟩
 | 6 => ⟨R7.Core.Certificates.Terminal067.polynomial_11, 59063636275557368681919084172063086961268338682750193142924431674048495374129072949483361939193978371444114267429353065642136943304979251200000000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_11⟩
theorem bound_43 : minorBindings polynomial_43 witness_43 := by
 decide +kernel
theorem positive_43 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_43 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_43 ρ hρ u
noncomputable def polynomial_44 : BiPoly := r7_rat_grid%[[7086646787358817620],[74459604591525000],[75488625948000332040],[3047662272051472500],[280948464569282796420],[3354669039543300000],[442884425318322638400],[-1713001328484187500],[309219153726907492560],[-1162771679403360000],[81958226248950030720],[0],[169881979092154560]]
noncomputable def witness_44 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal067.polynomial_12, 708664678735881762000, by norm_num, R7.Core.Certificates.Terminal067.positive_12⟩
 | 1 => ⟨R7.Core.Certificates.Terminal067.polynomial_13, 5242606179272184890386967353577602439040000, by norm_num, R7.Core.Certificates.Terminal067.positive_13⟩
 | 2 => ⟨R7.Core.Certificates.Terminal067.polynomial_14, 147231688573485849700355717495365287648628693872302255619260928000, by norm_num, R7.Core.Certificates.Terminal067.positive_14⟩
 | 3 => ⟨R7.Core.Certificates.Terminal067.polynomial_15, 6520514680090694061118894811092889719906911044855766584234305078674812445899243520000000, by norm_num, R7.Core.Certificates.Terminal067.positive_15⟩
 | 4 => ⟨R7.Core.Certificates.Terminal067.polynomial_16, 201625723042219944909815099615699312419239050730232709546419853905535552804936628525854385547402821120000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_16⟩
 | 5 => ⟨R7.Core.Certificates.Terminal067.polynomial_17, 1652466622711524112885699013977738060602961590303309153720707620296043594955186169955832207355887238103436897895386480640000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_17⟩
 | 6 => ⟨R7.Core.Certificates.Terminal067.polynomial_18, 28072430024996239693390846084525872660440534899183262933419074542137662541829041009944051918792141781256661875312665211428265371332771840000000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_18⟩
theorem bound_44 : minorBindings polynomial_44 witness_44 := by
 decide +kernel
theorem positive_44 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_44 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_44 ρ hρ u
noncomputable def polynomial_45 : BiPoly := r7_rat_grid%[[1574810397190848360],[15972820484550000],[14486417001562627320],[558534834883140000],[47318647173892050360],[546320985569550000],[66305689159424779800],[-248193219047400000],[41579444162031099840],[-152585938772280000],[9982091658525965280],[0],[18875775454683840]]
noncomputable def witness_45 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal067.polynomial_19, 157481039719084836000, by norm_num, R7.Core.Certificates.Terminal067.positive_19⟩
 | 1 => ⟨R7.Core.Certificates.Terminal067.polynomial_20, 223570291271124797686284619076619312960000, by norm_num, R7.Core.Certificates.Terminal067.positive_20⟩
 | 2 => ⟨R7.Core.Certificates.Terminal067.polynomial_21, 1057484272972308507914067077621478686724041797504714289617536000, by norm_num, R7.Core.Certificates.Terminal067.positive_21⟩
 | 3 => ⟨R7.Core.Certificates.Terminal067.polynomial_22, 7011555528795704775975296984213074001296399470719673399638519788663310301857280000000, by norm_num, R7.Core.Certificates.Terminal067.positive_22⟩
 | 4 => ⟨R7.Core.Certificates.Terminal067.polynomial_23, 29153495307609264557697805768066237396891966443266531050221836071396510036889307401999788911083520000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_23⟩
 | 5 => ⟨R7.Core.Certificates.Terminal067.polynomial_24, 29100878116890694120908837952251533255421179650640533801812258862968023134424100414874982395200981036866458990018560000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_24⟩
 | 6 => ⟨R7.Core.Certificates.Terminal067.polynomial_25, 54930164086855145137992768385841541520181150378267210280599915919693705576851862997737298600172491321353761455194072516816053207040000000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_25⟩
theorem bound_45 : minorBindings polynomial_45 witness_45 := by
 decide +kernel
theorem positive_45 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_45 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_45 ρ hρ u
noncomputable def polynomial_46 : BiPoly := r7_rat_grid%[[76581464238695440],[143634908710700000],[1774494772977787560],[1295949554374410000],[12959279641492190460],[2032856491167900000],[33205493795383598400],[-42345309689100000],[34922641727927654820],[-511218583185960000],[13922390997417793680],[0],[42470494773038640]]
noncomputable def witness_46 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal067.polynomial_26, 7658146423869544000, by norm_num, R7.Core.Certificates.Terminal067.positive_26⟩
 | 1 => ⟨R7.Core.Certificates.Terminal067.polynomial_27, 1280177930884966323265589103235118720000, by norm_num, R7.Core.Certificates.Terminal067.positive_27⟩
 | 2 => ⟨R7.Core.Certificates.Terminal067.polynomial_28, 1627967990687325272318035777990142749374317224988800808832000, by norm_num, R7.Core.Certificates.Terminal067.positive_28⟩
 | 3 => ⟨R7.Core.Certificates.Terminal067.polynomial_29, 5392522245490413266254259504677175654729139215268002222597181432562666106880000000, by norm_num, R7.Core.Certificates.Terminal067.positive_29⟩
 | 4 => ⟨R7.Core.Certificates.Terminal067.polynomial_30, 18832104941037877733798601648224527911476333596503879952308173282312713363664743988260986716160000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_30⟩
 | 5 => ⟨R7.Core.Certificates.Terminal067.polynomial_31, 26215269565089970082988277057007771475355374460948251368540097493435753311063199072173073010243708753518040186880000000000000, by norm_num, R7.Core.Certificates.Terminal067.positive_31⟩
 | 6 => ⟨R7.Core.Certificates.Terminal068.polynomial_0, 111337546903795251570027507341393104848994170965096813404024334766875395217597339677532442904505157561353808802432692025106104320000000000000000, by norm_num, R7.Core.Certificates.Terminal068.positive_0⟩
theorem bound_46 : minorBindings polynomial_46 witness_46 := by
 decide +kernel
theorem positive_46 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_46 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_46 ρ hρ u
noncomputable def polynomial_47 : BiPoly := r7_rat_grid%[[742495567974122240],[1191422342982575000],[15719478228385486060],[9611175209962852500],[108612892259226159240],[14407267477000950000],[272276205824157064200],[-340191845685450000],[283400982683637277680],[-3464925952704840000],[111904501224527926560],[0],[339763958184309120]]
noncomputable def witness_47 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal068.polynomial_1, 74249556797412224000, by norm_num, R7.Core.Certificates.Terminal068.positive_1⟩
 | 1 => ⟨R7.Core.Certificates.Terminal068.polynomial_2, 110833382572935695588665809309146049120000, by norm_num, R7.Core.Certificates.Terminal068.positive_2⟩
 | 2 => ⟨R7.Core.Certificates.Terminal068.polynomial_3, 1187165828198808181629215076412331192830871053351125853036432000, by norm_num, R7.Core.Certificates.Terminal068.positive_3⟩
 | 3 => ⟨R7.Core.Certificates.Terminal068.polynomial_4, 32266186703953914275805877948259489663782748352209520076165094237051645276293440000000, by norm_num, R7.Core.Certificates.Terminal068.positive_4⟩
 | 4 => ⟨R7.Core.Certificates.Terminal068.polynomial_5, 914426558457211988440253616741023378857398474524168066483459964302210414345462815705482362544241920000000000, by norm_num, R7.Core.Certificates.Terminal068.positive_5⟩
 | 5 => ⟨R7.Core.Certificates.Terminal068.polynomial_6, 10231876346710805382192968386831703180951124945283849008093957592777165428210407123464871269593945661255257836303339520000000000000, by norm_num, R7.Core.Certificates.Terminal068.positive_6⟩
 | 6 => ⟨R7.Core.Certificates.Terminal068.polynomial_7, 347642280721087164343266909336206422620591521734447657413969142850079213915161049722770264828526580531715653292671339111519271999242240000000000000000, by norm_num, R7.Core.Certificates.Terminal068.positive_7⟩
theorem bound_47 : minorBindings polynomial_47 witness_47 := by
 decide +kernel
theorem positive_47 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_47 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_47 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalL007
