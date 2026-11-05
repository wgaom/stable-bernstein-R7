import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal022
import R7.Certificates.Spectral.Terminal.Terminal023

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry015
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_90 : BiPoly := [[161246661337258848,3342181498941889770,18903577511702776320],[0,7526661097184738000,36807370188015600000],[1730066287811549688,107180933230524954820,316664490428264851920],[0,74246684102306193600,229405094331612840000],[7212333596082370560,805255361533772828250,1463644768185555350400],[0,115941379502345216400,494855583135119190000],[15104373618334176000,2044717846874946945000,2780541506428049340000],[0,-8845951833463361400,428016863197473480000],[16741797039252119520,2082942997316978958000,2254035424581163036800],[0,-30032722353790800000,115239022598700000000],[9191947799598779376,775020015193293807840,610851703720020063840],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_90 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_16, 13800, by norm_num, R7.Core.Certificates.Terminal022.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_17, 36800, by norm_num, R7.Core.Certificates.Terminal022.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_18, 128, by norm_num, R7.Core.Certificates.Terminal022.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_19, 345600000, by norm_num, R7.Core.Certificates.Terminal022.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_20, 21772800000000, by norm_num, R7.Core.Certificates.Terminal022.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_21, 19752284160000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_22, 734439289977372672000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_22⟩
theorem bound_90 : minorBindings polynomial_90 witness_90 := by
 decide +kernel
theorem positive_90 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_90 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_90 ρ hρ u
def polynomial_91 : BiPoly := [[204257668954612896,6089562143346601290,28974677585873120640],[0,8636877775518875400,42688720956039480000],[2116192697973831348,152641530828410387220,426031323435346238820],[0,73866841361491602900,249861351341578635000],[8517125122030254240,1006877968710270792375,1828939008289487444100],[0,104890026193084099800,502901246803434705000],[17194956239599065360,2379333818912200292700,3267115238176842092400],[0,-11838744173407397400,403371830052756180000],[18325084324925700000,2301430274480669850000,2497744615006998000000],[0,-26308664781920740800,100949383796461200000],[9639343488959781912,812742228322170940080,640583423812587412080],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_91 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal022.polynomial_24, 96600, by norm_num, R7.Core.Certificates.Terminal022.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal022.polynomial_25, 373262400, by norm_num, R7.Core.Certificates.Terminal022.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal022.polynomial_26, 556416, by norm_num, R7.Core.Certificates.Terminal022.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal022.polynomial_27, 10015488000, by norm_num, R7.Core.Certificates.Terminal022.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal022.polynomial_28, 31548787200000000, by norm_num, R7.Core.Certificates.Terminal022.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal022.polynomial_29, 42931589621760000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal022.polynomial_30, 1596303796765819502592000000000000, by norm_num, R7.Core.Certificates.Terminal022.positive_30⟩
theorem bound_91 : minorBindings polynomial_91 witness_91 := by
 decide +kernel
theorem positive_91 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_91 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_91 ρ hρ u
def polynomial_92 : BiPoly := [[198100491515614080,7914520551616339200,32894972689080067200],[0,6620773558335996000,37921901343955200000],[1965591613888156080,161797983795075841200,430614940267489597200],[0,51476991144719512200,206049236957669430000],[7563989168632320480,941636351662011336000,1709136105393574843200],[0,66222137665634256000,381460369241352600000],[14555123668576569600,2054469751954570782000,2845010614772788614000],[0,-11327753923982487000,279362370081668400000],[14727084911186002560,1864782083341892304000,2028952159586476070400],[0,-16749678295599897600,64270449175046400000],[7321020371361859680,617272578472534891200,486519056060192971200],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_92 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_0, 4416000, by norm_num, R7.Core.Certificates.Terminal023.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_1, 529920000, by norm_num, R7.Core.Certificates.Terminal023.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_2, 82944000, by norm_num, R7.Core.Certificates.Terminal023.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_3, 29859840000000, by norm_num, R7.Core.Certificates.Terminal023.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_4, 403107840000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_5, 4701849845760000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_6, 124876091520350945280000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_6⟩
theorem bound_92 : minorBindings polynomial_92 witness_92 := by
 decide +kernel
theorem positive_92 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_92 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_92 ρ hρ u
def polynomial_93 : BiPoly := [[144559818133015680,7303382826041310075,27281254876810711200],[0,3179271758704623000,25417447076690100000],[1361066135516079300,124929625694496979500,320080284516873762000],[0,24254859246831747900,126890358850010385000],[4948975142643117600,643252258592074175625,1166701222984985896500],[0,28419799689002700000,213648325251935625000],[8959639805420954400,1285242662172770568000,1791700602603956046000],[0,-7519306191027529500,141556351176779400000],[8490273354657004320,1081841967690036453000,1179338831617119868800],[0,-7765603922908764000,29797518700521000000],[3936501033014015820,331906485646938403800,261600524191095823800],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_93 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_8, 931500, by norm_num, R7.Core.Certificates.Terminal023.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_9, 5030100000, by norm_num, R7.Core.Certificates.Terminal023.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_10, 39366000000, by norm_num, R7.Core.Certificates.Terminal023.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_11, 14171760000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_12, 15943230000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_13, 2582803260000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_14, 34298242910252640000000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_14⟩
theorem bound_93 : minorBindings polynomial_93 witness_93 := by
 decide +kernel
theorem positive_93 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_93 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_93 ρ hρ u
def polynomial_94 : BiPoly := [[76295459570202720,4592305723457321550,15861262020055444800],[0,826301427549516000,12361656618529200000],[671694975968974200,66907948786381840500,166752877815222678000],[0,7447245998879703600,56136664245719340000],[2272862658102765120,304876404008002842750,552664725690087235800],[0,8148868503653268000,85430565475507800000],[3810421526443394400,552713846248702728000,773989456172309271000],[0,-3286429630415694000,51052542414153300000],[3332023904109347280,426298394185838037000,465287635826341675200],[0,-2557071788979902400,9811779638403600000],[1423531738875917160,120025223591881784400,94600927567259744400],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_94 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_16, 207000, by norm_num, R7.Core.Certificates.Terminal023.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_17, 1117800000, by norm_num, R7.Core.Certificates.Terminal023.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_18, 1458000000, by norm_num, R7.Core.Certificates.Terminal023.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_19, 262440000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_20, 9447840000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_21, 3061100160000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_22, 13549923125038080000000000000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_22⟩
theorem bound_94 : minorBindings polynomial_94 witness_94 := by
 decide +kernel
theorem positive_94 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_94 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_94 ρ hρ u
def polynomial_95 : BiPoly := [[26502633324386208,1781599057268884920,5879256561791838720],[0,97022594354202000,3982357592987400000],[214235344966946508,22381973598435927120,54928545777447390720],[0,1542419093593182600,16332812852160690000],[659863352352415680,90011078936243856000,163120603252843411200],[0,1620671534968251600,22334339174202360000],[1004097564400624200,146447177062783194000,205525708548349878000],[0,-850950933777642600,12004034854403070000],[797926528891050480,102278529813911877000,111696095313900763200],[0,-546309520911813600,2096252696795400000],[310852849101475788,26209589641492552920,20657753570809780920],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
def witness_95 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal023.polynomial_24, 49183200, by norm_num, R7.Core.Certificates.Terminal023.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal023.polynomial_25, 31870713600, by norm_num, R7.Core.Certificates.Terminal023.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal023.polynomial_26, 68024448, by norm_num, R7.Core.Certificates.Terminal023.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal023.polynomial_27, 330598817280000, by norm_num, R7.Core.Certificates.Terminal023.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal023.polynomial_28, 8926168066560000000, by norm_num, R7.Core.Certificates.Terminal023.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal023.polynomial_29, 289207845356544000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal023.polynomial_30, 256035011395319547494400000000000, by norm_num, R7.Core.Certificates.Terminal023.positive_30⟩
theorem bound_95 : minorBindings polynomial_95 witness_95 := by
 decide +kernel
theorem positive_95 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_95 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_95 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry015
