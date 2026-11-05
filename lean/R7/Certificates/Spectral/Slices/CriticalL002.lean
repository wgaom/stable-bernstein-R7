import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal060
import R7.Certificates.Spectral.Terminal.Terminal061

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalL002
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_12 : BiPoly := [[18242538282282852],[813077771580000],[143615737254746232],[7969598855730000],[397160041709270880],[6184327123980000],[473861399473038240],[-2085959936610000],[254526082275448980],[-1113765976440000],[52537324518557712],[0],[85798979339472]]
def witness_12 : Fin 7 → MinorWitness
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
def polynomial_13 : BiPoly := [[30564156148992],[2153544976440000],[41621288086212576],[67269230106300000],[424518521464477440],[116368394613210000],[1097707809174893640],[-114042462435000],[1069088747449078800],[-23389085505240000],[385273713136089888],[0],[1029587752073664]]
def witness_13 : Fin 7 → MinorWitness
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
def polynomial_14 : BiPoly := [[4630609753915424],[26700375154900000],[435748328231034656],[633254494526670000],[4213301590378280040],[1106499367971495000],[11031433532446811400],[-2504054525197500],[11030255584191386640],[-237789035969940000],[4097911312447501536],[0],[11325465272810304]]
def witness_14 : Fin 7 → MinorWitness
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
def polynomial_15 : BiPoly := [[47973743069579640],[173938762484950000],[2376095248196266840],[2885694951722985000],[20766999716610172530],[4891288284074475000],[53456739581116539000],[-30274001761162500],[53664433750628907120],[-1079796114158580000],[20139307732113789600],[0],[56627326364051520]]
def witness_15 : Fin 7 → MinorWitness
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
def polynomial_16 : BiPoly := [[244500757166922640],[672906206325625000],[8487050893422831960],[8274127306653412500],[66040710368595107340],[13241912227381350000],[163942636129789174200],[-187277062667062500],[162376592547676320000],[-2896905304720440000],[60417923196341368800],[0],[169881979092154560]]
def witness_16 : Fin 7 → MinorWitness
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
def polynomial_17 : BiPoly := [[797097504606769110],[1672825859898000000],[21566915734106747780],[16286577706770547500],[148929283608719728590],[24205098520773450000],[351670135430796003000],[-671129940418987500],[338779779801499559520],[-5118868427718240000],[122937339373425046080],[0],[339763958184309120]]
def witness_17 : Fin 7 → MinorWitness
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
