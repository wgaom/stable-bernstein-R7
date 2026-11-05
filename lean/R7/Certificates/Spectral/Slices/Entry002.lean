import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal003
import R7.Certificates.Spectral.Terminal.Terminal004

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry002
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_12 : BiPoly := [[1204665151108464,80981775330403860,267238934626901760],[0,3528094340152800,144813003381360000],[6363426088127124,664811096983245360,1631540963686556160],[0,38084422064029200,403279329682980000],[13747153174008660,1875230811171747000,3398345901100904400],[0,28854686082520800,397644020905680000],[15447654836932680,2253033493273587600,3161933977666921200],[0,-11422160184934800,161127984622860000],[9424329081390360,1208014131660376500,1319245220242922400],[0,-5720518543579200,21950290018800000],[2905166814032484,244949435901799560,193063117484203560],[0,0,0],[340100332584804,-1432692003894840,1708002866952360]]
def witness_12 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_0, 2235600, by norm_num, R7.Core.Certificates.Terminal003.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_1, 13038019200, by norm_num, R7.Core.Certificates.Terminal003.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_2, 1836660096, by norm_num, R7.Core.Certificates.Terminal003.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_3, 1785233613312000, by norm_num, R7.Core.Certificates.Terminal003.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_4, 289207845356544000000, by norm_num, R7.Core.Certificates.Terminal003.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_5, 9370334189552025600000000, by norm_num, R7.Core.Certificates.Terminal003.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_6, 62844957342487525294080000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_6⟩
theorem bound_12 : minorBindings polynomial_12 witness_12 := by
 decide +kernel
theorem positive_12 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_12 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_12 ρ hρ u
def polynomial_13 : BiPoly := [[634556128978944,-4253891940253440,17164285793544960],[0,9388005626750400,182240228364480000],[5865874254076032,164646837954288480,702666313262912880],[0,328508051799852000,1043872531993800000],[21723896373742080,1959203549689056000,3562158044667787200],[0,566225021005851600,2132699517949860000],[41193746231820480,5187662140407618600,6810220136638123200],[0,-13140112002715800,1777343278714560000],[41885907028401600,5060600445380490000,5425296347408544000],[0,-120130889415163200,460956090394800000],[21304556636238216,1796295863279863440,1415796194884159440],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
def witness_13 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_8, 5299200, by norm_num, R7.Core.Certificates.Terminal003.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_9, 254361600, by norm_num, R7.Core.Certificates.Terminal003.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_10, 221184, by norm_num, R7.Core.Certificates.Terminal003.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_11, 71663616000, by norm_num, R7.Core.Certificates.Terminal003.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_12, 3224862720000000, by norm_num, R7.Core.Certificates.Terminal003.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_13, 69657034752000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_14, 5606109608096563200000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_14⟩
theorem bound_13 : minorBindings polynomial_13 witness_13 := by
 decide +kernel
theorem positive_13 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_13 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_13 ρ hρ u
def polynomial_14 : BiPoly := [[6028283225299968,-19201927979427680,221598872110677120],[0,121031336350244000,1660487563432800000],[56144796431870592,1760352718332126880,7060261670751023280],[0,3093900694344466800,9685878338784420000],[211807989643985280,19469212930727301000,35402380770263425200],[0,5384135795285590200,20311116271786170000],[411937462318204800,52145336683528641000,68641212748576482000],[0,-135903761693664300,17459901719654760000],[431424842392536480,52216689962685402000,56011957101076003200],[0,-1221330709054159200,4686386919013800000],[226603011494533752,19106056000340365680,15058923163767877680],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
def witness_14 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_16, 73600, by norm_num, R7.Core.Certificates.Terminal003.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_17, 2355200, by norm_num, R7.Core.Certificates.Terminal003.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_18, 8192, by norm_num, R7.Core.Certificates.Terminal003.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_19, 33914880000, by norm_num, R7.Core.Certificates.Terminal003.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_20, 3317760000000, by norm_num, R7.Core.Certificates.Terminal003.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_21, 644972544000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_22, 570992645269094400000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_22⟩
theorem bound_14 : minorBindings polynomial_14 witness_14 := by
 decide +kernel
theorem positive_14 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_14 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_14 ρ hρ u
def polynomial_15 : BiPoly := [[28555025804052480,35672172108730200,1483946203443523200],[0,815035703458862000,7415460786254400000],[266059296524162880,9877228486773198200,36329148130306084200],[0,14110770490025459400,43064551764034110000],[1007445694332288960,96196181251337888250,174945662421246131400],[0,23800759094903751000,90401836548870225000],[1973867006941398000,252818454215047995000,334815904726401195000],[0,-702957054436780500,78245834889668850000],[2090106760717239840,254096553604014486000,272956168022742345600],[0,-5546042728000034400,21280806173226600000],[1113647278712452200,93897283762356498000,74007528368944698000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_15 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_24, 828000, by norm_num, R7.Core.Certificates.Terminal003.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_25, 7360000, by norm_num, R7.Core.Certificates.Terminal003.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal003.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_27, 345600000000, by norm_num, R7.Core.Certificates.Terminal003.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_28, 777600000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_29, 419904000000000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_30, 1858700017152000000000000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_30⟩
theorem bound_15 : minorBindings polynomial_15 witness_15 := by
 decide +kernel
theorem positive_15 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_15 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_15 ρ hρ u
def polynomial_16 : BiPoly := [[88044662895828480,579144012327285200,6273974802859363200],[0,3212629248215645000,21265560443799000000],[812842575207678720,36233425950197575800,122469064371305659800],[0,40497668287029766500,121043626139684475000],[3056280671080838880,306857484366480613500,558070965683953999200],[0,64425668855618646000,249286021884471600000],[5955929142684044400,775918215506995443000,1036299222092031021000],[0,-2424926066162512500,212216083255327500000],[6282886054260240000,769080647335839840000,827986162170225600000],[0,-14879068731849499200,57092704338898800000],[3340941836137356600,281691851287069494000,222022585106834094000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_16 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_0, 184000, by norm_num, R7.Core.Certificates.Terminal004.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_1, 3680000, by norm_num, R7.Core.Certificates.Terminal004.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_2, 384000, by norm_num, R7.Core.Certificates.Terminal004.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_3, 69120000000, by norm_num, R7.Core.Certificates.Terminal004.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_4, 58320000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_5, 3779136000000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_6, 50184900463104000000000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_6⟩
theorem bound_16 : minorBindings polynomial_16 witness_16 := by
 decide +kernel
theorem positive_16 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_16 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_16 ρ hρ u
def polynomial_17 : BiPoly := [[194531113290107520,2529559393480373550,18164456769679876800],[0,8068119819805200000,43409376682627500000],[1766832749654061960,94149225707022616900,295156705285647176400],[0,79770460451614911900,238692517517696985000],[6535498449687968880,694289670448859979750,1262420277050390074200],[0,117707464443724362000,473865412762605825000],[12529764478845396000,1665840357391166055000,2246584204268071515000],[0,-6056524201391401500,388374229608679800000],[13001385541615856640,1605222377845188156000,1732894543105308057600],[0,-26291503226290003200,100883532926404800000],[6798090344836012560,573181680010210970400,451767694913036330400],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_17 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_8, 69000, by norm_num, R7.Core.Certificates.Terminal004.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_9, 2760000, by norm_num, R7.Core.Certificates.Terminal004.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal004.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_11, 14400000000, by norm_num, R7.Core.Certificates.Terminal004.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_12, 32400000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_13, 188956800000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_14, 5018490046310400000000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_14⟩
theorem bound_17 : minorBindings polynomial_17 witness_17 := by
 decide +kernel
theorem positive_17 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_17 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_17 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry002
