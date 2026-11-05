import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal004
import R7.Certificates.Spectral.Terminal.Terminal005

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry003
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_18 : BiPoly := [[322493322674517696,6684362997883779540,37807155023405552640],[0,13563342879487702600,66156218311434120000],[2858199604175815128,179748059997469496420,528024752439480641520],[0,111363238264093052400,346836324863217060000],[10308667701102296400,1160451698400335235000,2109079469358442926000],[0,150731427405674341800,652835110675269780000],[19244345114632134240,2614643385506688331800,3561374087485325346600],[0,-11086756107255693900,505082261845662480000],[19409929316961301440,2418901535851870356000,2618943296157983289600],[0,-32315209252678900800,123997188316201200000],[9842705165942055792,829888688835296909280,654097842036481661280],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_18 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_16, 27600, by norm_num, R7.Core.Certificates.Terminal004.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_17, 73600, by norm_num, R7.Core.Certificates.Terminal004.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_18, 128, by norm_num, R7.Core.Certificates.Terminal004.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_19, 13824000, by norm_num, R7.Core.Certificates.Terminal004.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_20, 217728000000, by norm_num, R7.Core.Certificates.Terminal004.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_21, 197522841600000000, by norm_num, R7.Core.Certificates.Terminal004.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_22, 7344392899773726720000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_22⟩
theorem bound_18 : minorBindings polynomial_18 witness_18 := by
 decide +kernel
theorem positive_18 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_18 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_18 ρ hρ u
def polynomial_19 : BiPoly := [[408515337909225792,12179124286693202580,57949355171746241280],[0,15497064088954413000,76918452904200600000],[3505540727214920088,255791805865596508320,710905203804176062920],[0,110623916450562585000,379562788785755250000],[12213581864374805040,1453382938576486911750,2639745303237422328600],[0,136330154561014734600,666999684022321035000],[21969997990304256000,3048891021929176425000,4191732733181856165000],[0,-14733815461929792900,478522854078636780000],[21286417951833693120,2676698241894411588000,2906148559371934060800],[0,-28471020791393678400,109246593423567600000],[10330773190699513104,871040194066799235360,686532445773827859360],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_19 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_24, 193200, by norm_num, R7.Core.Certificates.Terminal004.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_25, 64915200, by norm_num, R7.Core.Certificates.Terminal004.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_26, 193536, by norm_num, R7.Core.Certificates.Terminal004.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_27, 174182400000, by norm_num, R7.Core.Certificates.Terminal004.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_28, 8230118400000000, by norm_num, R7.Core.Certificates.Terminal004.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_29, 7466363412480000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_30, 277618051611446870016000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_30⟩
theorem bound_19 : minorBindings polynomial_19 witness_19 := by
 decide +kernel
theorem positive_19 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_19 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_19 ρ hρ u
def polynomial_20 : BiPoly := [[396200983031228160,15829041103232678400,65789945378160134400],[0,11824345664128194000,68424479574022800000],[3259488251807337960,270532343123438054400,717879013837779641400],[0,76900466473445259300,314002290857055795000],[10857196084539283920,1357995468772247041500,2464661153737069552800],[0,86058256778603856000,508082032894962600000],[18605842048038916800,2631474784136234961000,3647075919985802187000],[0,-13970293982397787500,333271668085695000000],[17106204430399213440,2167765091684251776000,2359184985544305369600],[0,-18259895191104806400,70065325740009600000],[7843950397887706800,661363476934858812000,521270417207349612000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_20 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_0, 8832000, by norm_num, R7.Core.Certificates.Terminal005.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_1, 132480000, by norm_num, R7.Core.Certificates.Terminal005.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_2, 10368000, by norm_num, R7.Core.Certificates.Terminal005.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_3, 1866240000000, by norm_num, R7.Core.Certificates.Terminal005.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_4, 4199040000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_5, 8448636441600000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_6, 224386726950630604800000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_6⟩
theorem bound_20 : minorBindings polynomial_20 witness_20 := by
 decide +kernel
theorem positive_20 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_20 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_20 ρ hρ u
def polynomial_21 : BiPoly := [[289119636266031360,14606765652082620150,54562509753621422400],[0,5647255248712995000,45888335041756500000],[2255481024569502840,208106200242757520100,532225663878929655600],[0,36191756133843133500,193643646474638025000],[7093531037788468560,924604458794682608250,1676920401979769795400],[0,37041632998436646000,285445545748755975000],[11431264579330183200,1641590181880023384000,2289490595868575313000],[0,-9187596461910793500,169782429102694200000],[9843188151674376000,1254734910352994490000,1367979185360751840000],[0,-8529293148476587200,32727882418030800000],[4212491880347101800,355176682057609362000,279941520352095162000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_21 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_8, 1863000, by norm_num, R7.Core.Certificates.Terminal005.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_9, 2012040000, by norm_num, R7.Core.Certificates.Terminal005.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_10, 314928000, by norm_num, R7.Core.Certificates.Terminal005.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_11, 56687040000000, by norm_num, R7.Core.Certificates.Terminal005.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_12, 3188646000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_13, 1033121304000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_14, 13719297164101056000000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_14⟩
theorem bound_21 : minorBindings polynomial_21 witness_21 := by
 decide +kernel
theorem positive_21 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_21 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_21 ρ hρ u
def polynomial_22 : BiPoly := [[152590919140405440,9184611446914643100,31722524040110889600],[0,1462197930604020000,22296625347924000000],[1110064328706620520,110839443209884995300,276024873398377546800],[0,11169570017294929800,85611421683732870000],[3244328149066043760,435672129073342077000,789749459381685938400],[0,10727110993613850000,114244032236366250000],[4840265182238906400,702364367238072408000,983702462261825601000],[0,-3980407722135831000,61428741501364200000],[3849314855910107040,492543277384574466000,537611936988941193600],[0,-2823075901256335200,10832468124277800000],[1520370632676999960,128190204788608436400,101036364816733196400],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_22 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_16, 414000, by norm_num, R7.Core.Certificates.Terminal005.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_17, 447120000, by norm_num, R7.Core.Certificates.Terminal005.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_18, 11664000, by norm_num, R7.Core.Certificates.Terminal005.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_19, 2099520000000, by norm_num, R7.Core.Certificates.Terminal005.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_20, 18895680000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_21, 2040733440000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_22, 9033282083358720000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_22⟩
theorem bound_22 : minorBindings polynomial_22 witness_22 := by
 decide +kernel
theorem positive_22 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_22 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_22 ρ hρ u
def polynomial_23 : BiPoly := [[53005266648772416,3563198114537769840,11758513123583677440],[0,174640669837563600,7168243667377320000],[352109576876367528,36786214033072909920,90278599990656107520],[0,2342191956937795800,24801678775503270000],[934806415832588880,127515695159678796000,231087521274861499200],[0,2159292341841973200,29757027564441720000],[1266707696628479760,184748746448434183200,259278586168687538400],[0,-1022283336551664600,14420954623745970000],[917301363921995040,117580042148276646000,128406534770311113600],[0,-603514706347605600,2315755596983400000],[331189016799703176,27924235692805149840,22009195393199205840],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
def witness_23 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_24, 98366400, by norm_num, R7.Core.Certificates.Terminal005.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_25, 127482854400, by norm_num, R7.Core.Certificates.Terminal005.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_26, 544195584, by norm_num, R7.Core.Certificates.Terminal005.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_27, 1057916215296000, by norm_num, R7.Core.Certificates.Terminal005.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_28, 14281868906496000000, by norm_num, R7.Core.Certificates.Terminal005.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_29, 2776395315422822400000000, by norm_num, R7.Core.Certificates.Terminal005.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_30, 2457936109395067655946240000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_30⟩
theorem bound_23 : minorBindings polynomial_23 witness_23 := by
 decide +kernel
theorem positive_23 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_23 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_23 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry003
