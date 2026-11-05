import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal037
import R7.Certificates.Spectral.Terminal.Terminal038

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry025
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_150 : BiPoly := [[213195986927652240,5832235776285793850,24955979673642351600],[0,9967353280387745000,39705009284281500000],[2388772542217926960,150353544973236730650,437168849694512463900],[0,99397686914814404400,286936982504748360000],[10999080282730286880,1222394855907618804750,2222572240577008069200],[0,179040975956665578000,732744758597946300000],[25986388247906752800,3505041716065942851000,4759430917953715677000],[0,-13454641907718669000,751098335778573300000],[32677290368207508240,4056489989963390511000,4386616982876255601600],[0,-61987538938224211200,237853342643716800000],[20336167698227388000,1714646051312596920000,1351441822389424920000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_150 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal037.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_17, 460000, by norm_num, R7.Core.Certificates.Terminal037.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_18, 6000, by norm_num, R7.Core.Certificates.Terminal037.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_19, 1080000000, by norm_num, R7.Core.Certificates.Terminal037.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_20, 204120000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_21, 46294416000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_22, 4303355214711168000000000000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_22⟩
theorem bound_150 : minorBindings polynomial_150 witness_150 := by
 decide +kernel
theorem positive_150 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_150 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_150 ρ hρ u
def polynomial_151 : BiPoly := [[315354566223504576,10974203492367276990,43681212875679171840],[0,12877343561766297600,52339686816610620000],[3444970338153858204,248105232197339349060,687210979068613840860],[0,115476085486984023000,360408071284587450000],[15386628478464507600,1804521804302566869375,3278928057312080371500],[0,191367137559889279800,866345940690612705000],[35155429596672794640,4843952989575895842300,6640127508442988307600],[0,-21452857181508778200,828734902388661240000],[42631476173507148480,5342350270860150282000,5794137207967712083200],[0,-63789502279451659200,244767683999638800000],[25501554293577144552,2150166148345996537680,1694708045276338849680],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
def witness_151 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal037.polynomial_24, 41400, by norm_num, R7.Core.Certificates.Terminal037.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal037.polynomial_25, 146059200, by norm_num, R7.Core.Certificates.Terminal037.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal037.polynomial_26, 31104, by norm_num, R7.Core.Certificates.Terminal037.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal037.polynomial_27, 1679616000, by norm_num, R7.Core.Certificates.Terminal037.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal037.polynomial_28, 211631616000000, by norm_num, R7.Core.Certificates.Terminal037.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal037.polynomial_29, 287988303052800000000, by norm_num, R7.Core.Certificates.Terminal037.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal037.polynomial_30, 32124374543610280673280000000000, by norm_num, R7.Core.Certificates.Terminal037.positive_30⟩
theorem bound_151 : minorBindings polynomial_151 witness_151 := by
 decide +kernel
theorem positive_151 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_151 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_151 ρ hρ u
def polynomial_152 : BiPoly := [[349352893821454560,15031665973665290650,56031855430690010400],[0,10780165119420588000,51518393798385600000],[3682538245443937500,299406217085044920000,795293636924807437500],[0,90631249785454902600,333672626133116190000],[15798024766042248240,1948119904939276144875,3537161088476164716600],[0,137828717799455214000,743330318521756275000],[34516926530079577200,4851916783983511456500,6708041965331021898000],[0,-24202124834568219000,651678672115270800000],[39846063356118442080,5036254609704978492000,5476587154655715907200],[0,-46130261535422668800,177007138711603200000],[22573146145032400680,1903257116956982581200,1500100422852261661200],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_152 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_0, 23000, by norm_num, R7.Core.Certificates.Terminal038.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_1, 1035000000, by norm_num, R7.Core.Certificates.Terminal038.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_2, 11250000000, by norm_num, R7.Core.Certificates.Terminal038.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_3, 1012500000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_4, 3444525000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_5, 23436548100000000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_6, 2178573577447528800000000000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_6⟩
theorem bound_152 : minorBindings polynomial_152 witness_152 := by
 decide +kernel
theorem positive_152 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_152 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_152 ρ hρ u
def polynomial_153 : BiPoly := [[286442602596901440,14794814843949960600,51958954632866529600],[0,5312616056398827000,37646908785099900000],[2884753159950962880,259919100767490065700,667086375694866896700],[0,46024037301788035500,226857634772039325000],[11749233579386068080,1512465108117236574750,2744093592917389627200],[0,64895979420370836000,462477796375564350000],[24235654033054382400,3464132700700737243000,4822601919671494566000],[0,-18703827847343556000,367410188136859200000],[26262463706807803200,3341911294489931460000,3641605833599525088000],[0,-23785916104202313600,91269305898170400000],[13886697371075273520,1170858303610601896800,922841701574493016800],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_153 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_8, 276000, by norm_num, R7.Core.Certificates.Terminal038.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_9, 33120000, by norm_num, R7.Core.Certificates.Terminal038.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_10, 1296000, by norm_num, R7.Core.Certificates.Terminal038.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_11, 5365440000000, by norm_num, R7.Core.Certificates.Terminal038.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_12, 1007769600000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_13, 653034700800000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_14, 34687803200097484800000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_14⟩
theorem bound_153 : minorBindings polynomial_153 witness_153 := by
 decide +kernel
theorem positive_153 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_153 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_153 ρ hρ u
def polynomial_154 : BiPoly := [[167983862737902480,10006224255700442700,33504734300588773200],[0,1117867079525829000,19816383286347300000],[1590856522031781000,155116008566554496250,388054058124200602500],[0,14193327710655386400,110028549363576660000],[6060967088274040320,805818263081368760250,1461147932781780441300],[0,19402267657572378000,203994382412723175000],[11620069249559360400,1680739265218788063000,2351105748906632023500],[0,-9394616649230478000,146351310715963350000],[11636952120165674520,1487435428003676800500,1623017667296694736800],[0,-8649424037891750400,33188838508425600000],[5665075287363343800,477651400008509142000,376473079094196942000],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
def witness_154 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_16, 138000, by norm_num, R7.Core.Certificates.Terminal038.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_17, 621000000, by norm_num, R7.Core.Certificates.Terminal038.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_18, 37968750000, by norm_num, R7.Core.Certificates.Terminal038.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_19, 10251562500000000, by norm_num, R7.Core.Certificates.Terminal038.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_20, 184528125000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_21, 896806687500000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_22, 17863668182423250000000000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_22⟩
theorem bound_154 : minorBindings polynomial_154 witness_154 := by
 decide +kernel
theorem positive_154 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_154 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_154 ρ hρ u
def polynomial_155 : BiPoly := [[7138756451013120,96222201679163800,505962621203380800],[0,338157392968994000,1707565418182800000],[85893158720399040,3874974446646790600,12860396785394688600],[0,4707918875029392600,13427289733584690000],[418185005194535040,41367520567852034250,75268785211513653600],[0,10054137022033734000,37944097527607650000],[1047007716725437200,135134130572846109000,179692557328528173000],[0,-399474658605105000,43423831322473500000],[1396894999397193360,170112352794801489000,182839001666210942400],[0,-3964319350700385600,15211550983028400000],[919969491110286600,77567321368903194000,61136653869997794000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_155 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal038.polynomial_24, 92000, by norm_num, R7.Core.Certificates.Terminal038.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal038.polynomial_25, 7360000, by norm_num, R7.Core.Certificates.Terminal038.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal038.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal038.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal038.polynomial_27, 23040000000, by norm_num, R7.Core.Certificates.Terminal038.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal038.polynomial_28, 207360000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal038.polynomial_29, 2575411200000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal038.polynomial_30, 11400026771865600000000000000000, by norm_num, R7.Core.Certificates.Terminal038.positive_30⟩
theorem bound_155 : minorBindings polynomial_155 witness_155 := by
 decide +kernel
theorem positive_155 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_155 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_155 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry025
