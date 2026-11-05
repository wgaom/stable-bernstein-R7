import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal057
import R7.Certificates.Spectral.Terminal.Terminal058
import R7.Certificates.Spectral.Terminal.Terminal059

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL000
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_0 : BiPoly := [[5094026024832],[331314611760000],[5945898298030368],[8969230680840000],[53064815183059680],[13690399366260000],[121967534352765960],[-12004469730000],[106908874744907880],[-2227531952880000],[35024883012371808],[0],[85798979339472]]
def witness_0 : Fin 7 → MinorWitness
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
def polynomial_1 : BiPoly := [[45846234223488],[3064660158780000],[56486033831288496],[87449999138190000],[530648151830596800],[140326593504165000],[1280659110704042580],[-129048049597500],[1175997622193986680],[-25059734469900000],[402786154642275792],[0],[1029587752073664]]
def witness_1 : Fin 7 → MinorWitness
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
def polynomial_2 : BiPoly := [[3472957315436568],[19341944979420000],[301541178406646928],[416080294551990000],[2682392856136172910],[671579283306240000],[6535537784808193620],[-1673214629130000],[6134514193245382380],[-126969321314160000],[2154030305260866192],[0],[5662732636405152]]
def witness_2 : Fin 7 → MinorWitness
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
def polynomial_3 : BiPoly := [[23986871534789820],[84201281337075000],[1104380609807003820],[1274047712814172500],[8913626845312662405],[1991524901063625000],[21351523582101352500],[-13321467989775000],[20078316280919382120],[-383692378883580000],[7092538810005291120],[0],[18875775454683840]]
def witness_3 : Fin 7 → MinorWitness
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
def polynomial_4 : BiPoly := [[91687783937595990],[243890742134025000],[2969299193300158230],[2751629669975205000],[21410857725311151945],[4061603452833450000],[49497480518437613700],[-59934263677200000],[45878331370255541460],[-771839821672920000],[16023883978160102160],[0],[42470494773038640]]
def witness_4 : Fin 7 → MinorWitness
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
def polynomial_5 : BiPoly := [[239129251382030733],[484217951946465000],[6046890794958715692],[4341418867054462500],[38797968922821068445],[5954018735762955000],[85387358742362893980],[-167620705410015000],[76941581512343897520],[-1092604422887640000],[26163587610241740576],[0],[67952791636861824]]
def witness_5 : Fin 7 → MinorWitness
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
