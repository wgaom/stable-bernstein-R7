import R7.Spectral.SliceInteger
import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch00
import R7.Certificates.Spectral.Terminal.Batches.Batch01
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.Entry002
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_12 : BiPoly := r7_rat_grid%[[1204665151108464,80981775330403860,267238934626901760],[0,3528094340152800,144813003381360000],[6363426088127124,664811096983245360,1631540963686556160],[0,38084422064029200,403279329682980000],[13747153174008660,1875230811171747000,3398345901100904400],[0,28854686082520800,397644020905680000],[15447654836932680,2253033493273587600,3161933977666921200],[0,-11422160184934800,161127984622860000],[9424329081390360,1208014131660376500,1319245220242922400],[0,-5720518543579200,21950290018800000],[2905166814032484,244949435901799560,193063117484203560],[0,0,0],[340100332584804,-1432692003894840,1708002866952360]]
noncomputable def witness_12 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_0, 2235600, by norm_num, R7.Core.Certificates.Terminal003.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_1, 13038019200, by norm_num, R7.Core.Certificates.Terminal003.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_2, 1836660096, by norm_num, R7.Core.Certificates.Terminal003.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_3, 1785233613312000, by norm_num, R7.Core.Certificates.Terminal003.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_4, 289207845356544000000, by norm_num, R7.Core.Certificates.Terminal003.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_5, 9370334189552025600000000, by norm_num, R7.Core.Certificates.Terminal003.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_6, 62844957342487525294080000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_6⟩
theorem bound_12 : minorBindings polynomial_12 witness_12 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_12 witness_12 (by decide +kernel)
theorem positive_12 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_12 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_12 ρ hρ u
noncomputable def polynomial_13 : BiPoly := r7_rat_grid%[[634556128978944,-4253891940253440,17164285793544960],[0,9388005626750400,182240228364480000],[5865874254076032,164646837954288480,702666313262912880],[0,328508051799852000,1043872531993800000],[21723896373742080,1959203549689056000,3562158044667787200],[0,566225021005851600,2132699517949860000],[41193746231820480,5187662140407618600,6810220136638123200],[0,-13140112002715800,1777343278714560000],[41885907028401600,5060600445380490000,5425296347408544000],[0,-120130889415163200,460956090394800000],[21304556636238216,1796295863279863440,1415796194884159440],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
noncomputable def witness_13 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_8, 5299200, by norm_num, R7.Core.Certificates.Terminal003.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_9, 254361600, by norm_num, R7.Core.Certificates.Terminal003.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_10, 221184, by norm_num, R7.Core.Certificates.Terminal003.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_11, 71663616000, by norm_num, R7.Core.Certificates.Terminal003.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_12, 3224862720000000, by norm_num, R7.Core.Certificates.Terminal003.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_13, 69657034752000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_14, 5606109608096563200000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_14⟩
theorem bound_13 : minorBindings polynomial_13 witness_13 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_13 witness_13 (by decide +kernel)
theorem positive_13 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_13 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_13 ρ hρ u
noncomputable def polynomial_14 : BiPoly := r7_rat_grid%[[6028283225299968,-19201927979427680,221598872110677120],[0,121031336350244000,1660487563432800000],[56144796431870592,1760352718332126880,7060261670751023280],[0,3093900694344466800,9685878338784420000],[211807989643985280,19469212930727301000,35402380770263425200],[0,5384135795285590200,20311116271786170000],[411937462318204800,52145336683528641000,68641212748576482000],[0,-135903761693664300,17459901719654760000],[431424842392536480,52216689962685402000,56011957101076003200],[0,-1221330709054159200,4686386919013800000],[226603011494533752,19106056000340365680,15058923163767877680],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
noncomputable def witness_14 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_16, 73600, by norm_num, R7.Core.Certificates.Terminal003.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_17, 2355200, by norm_num, R7.Core.Certificates.Terminal003.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_18, 8192, by norm_num, R7.Core.Certificates.Terminal003.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_19, 33914880000, by norm_num, R7.Core.Certificates.Terminal003.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_20, 3317760000000, by norm_num, R7.Core.Certificates.Terminal003.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_21, 644972544000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_22, 570992645269094400000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_22⟩
theorem bound_14 : minorBindings polynomial_14 witness_14 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_14 witness_14 (by decide +kernel)
theorem positive_14 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_14 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_14 ρ hρ u
noncomputable def polynomial_15 : BiPoly := r7_rat_grid%[[28555025804052480,35672172108730200,1483946203443523200],[0,815035703458862000,7415460786254400000],[266059296524162880,9877228486773198200,36329148130306084200],[0,14110770490025459400,43064551764034110000],[1007445694332288960,96196181251337888250,174945662421246131400],[0,23800759094903751000,90401836548870225000],[1973867006941398000,252818454215047995000,334815904726401195000],[0,-702957054436780500,78245834889668850000],[2090106760717239840,254096553604014486000,272956168022742345600],[0,-5546042728000034400,21280806173226600000],[1113647278712452200,93897283762356498000,74007528368944698000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_15 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal003.polynomial_24, 828000, by norm_num, R7.Core.Certificates.Terminal003.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal003.polynomial_25, 7360000, by norm_num, R7.Core.Certificates.Terminal003.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal003.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal003.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal003.polynomial_27, 345600000000, by norm_num, R7.Core.Certificates.Terminal003.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal003.polynomial_28, 777600000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal003.polynomial_29, 419904000000000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal003.polynomial_30, 1858700017152000000000000000000, by norm_num, R7.Core.Certificates.Terminal003.positive_30⟩
theorem bound_15 : minorBindings polynomial_15 witness_15 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_15 witness_15 (by decide +kernel)
theorem positive_15 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_15 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_15 ρ hρ u
noncomputable def polynomial_16 : BiPoly := r7_rat_grid%[[88044662895828480,579144012327285200,6273974802859363200],[0,3212629248215645000,21265560443799000000],[812842575207678720,36233425950197575800,122469064371305659800],[0,40497668287029766500,121043626139684475000],[3056280671080838880,306857484366480613500,558070965683953999200],[0,64425668855618646000,249286021884471600000],[5955929142684044400,775918215506995443000,1036299222092031021000],[0,-2424926066162512500,212216083255327500000],[6282886054260240000,769080647335839840000,827986162170225600000],[0,-14879068731849499200,57092704338898800000],[3340941836137356600,281691851287069494000,222022585106834094000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_16 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_0, 184000, by norm_num, R7.Core.Certificates.Terminal004.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_1, 3680000, by norm_num, R7.Core.Certificates.Terminal004.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_2, 384000, by norm_num, R7.Core.Certificates.Terminal004.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_3, 69120000000, by norm_num, R7.Core.Certificates.Terminal004.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_4, 58320000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_5, 3779136000000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_6, 50184900463104000000000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_6⟩
theorem bound_16 : minorBindings polynomial_16 witness_16 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_16 witness_16 (by decide +kernel)
theorem positive_16 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_16 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_16 ρ hρ u
noncomputable def polynomial_17 : BiPoly := r7_rat_grid%[[194531113290107520,2529559393480373550,18164456769679876800],[0,8068119819805200000,43409376682627500000],[1766832749654061960,94149225707022616900,295156705285647176400],[0,79770460451614911900,238692517517696985000],[6535498449687968880,694289670448859979750,1262420277050390074200],[0,117707464443724362000,473865412762605825000],[12529764478845396000,1665840357391166055000,2246584204268071515000],[0,-6056524201391401500,388374229608679800000],[13001385541615856640,1605222377845188156000,1732894543105308057600],[0,-26291503226290003200,100883532926404800000],[6798090344836012560,573181680010210970400,451767694913036330400],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_17 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_8, 69000, by norm_num, R7.Core.Certificates.Terminal004.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_9, 2760000, by norm_num, R7.Core.Certificates.Terminal004.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal004.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_11, 14400000000, by norm_num, R7.Core.Certificates.Terminal004.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_12, 32400000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_13, 188956800000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_14, 5018490046310400000000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_14⟩
theorem bound_17 : minorBindings polynomial_17 witness_17 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_17 witness_17 (by decide +kernel)
theorem positive_17 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_17 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_17 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry002

namespace R7.Core.SpectralSliceCertificates.Entry003
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_18 : BiPoly := r7_rat_grid%[[322493322674517696,6684362997883779540,37807155023405552640],[0,13563342879487702600,66156218311434120000],[2858199604175815128,179748059997469496420,528024752439480641520],[0,111363238264093052400,346836324863217060000],[10308667701102296400,1160451698400335235000,2109079469358442926000],[0,150731427405674341800,652835110675269780000],[19244345114632134240,2614643385506688331800,3561374087485325346600],[0,-11086756107255693900,505082261845662480000],[19409929316961301440,2418901535851870356000,2618943296157983289600],[0,-32315209252678900800,123997188316201200000],[9842705165942055792,829888688835296909280,654097842036481661280],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_18 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_16, 27600, by norm_num, R7.Core.Certificates.Terminal004.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_17, 73600, by norm_num, R7.Core.Certificates.Terminal004.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_18, 128, by norm_num, R7.Core.Certificates.Terminal004.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_19, 13824000, by norm_num, R7.Core.Certificates.Terminal004.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_20, 217728000000, by norm_num, R7.Core.Certificates.Terminal004.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_21, 197522841600000000, by norm_num, R7.Core.Certificates.Terminal004.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_22, 7344392899773726720000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_22⟩
theorem bound_18 : minorBindings polynomial_18 witness_18 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_18 witness_18 (by decide +kernel)
theorem positive_18 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_18 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_18 ρ hρ u
noncomputable def polynomial_19 : BiPoly := r7_rat_grid%[[408515337909225792,12179124286693202580,57949355171746241280],[0,15497064088954413000,76918452904200600000],[3505540727214920088,255791805865596508320,710905203804176062920],[0,110623916450562585000,379562788785755250000],[12213581864374805040,1453382938576486911750,2639745303237422328600],[0,136330154561014734600,666999684022321035000],[21969997990304256000,3048891021929176425000,4191732733181856165000],[0,-14733815461929792900,478522854078636780000],[21286417951833693120,2676698241894411588000,2906148559371934060800],[0,-28471020791393678400,109246593423567600000],[10330773190699513104,871040194066799235360,686532445773827859360],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_19 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal004.polynomial_24, 193200, by norm_num, R7.Core.Certificates.Terminal004.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal004.polynomial_25, 64915200, by norm_num, R7.Core.Certificates.Terminal004.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal004.polynomial_26, 193536, by norm_num, R7.Core.Certificates.Terminal004.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal004.polynomial_27, 174182400000, by norm_num, R7.Core.Certificates.Terminal004.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal004.polynomial_28, 8230118400000000, by norm_num, R7.Core.Certificates.Terminal004.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal004.polynomial_29, 7466363412480000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal004.polynomial_30, 277618051611446870016000000000000, by norm_num, R7.Core.Certificates.Terminal004.positive_30⟩
theorem bound_19 : minorBindings polynomial_19 witness_19 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_19 witness_19 (by decide +kernel)
theorem positive_19 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_19 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_19 ρ hρ u
noncomputable def polynomial_20 : BiPoly := r7_rat_grid%[[396200983031228160,15829041103232678400,65789945378160134400],[0,11824345664128194000,68424479574022800000],[3259488251807337960,270532343123438054400,717879013837779641400],[0,76900466473445259300,314002290857055795000],[10857196084539283920,1357995468772247041500,2464661153737069552800],[0,86058256778603856000,508082032894962600000],[18605842048038916800,2631474784136234961000,3647075919985802187000],[0,-13970293982397787500,333271668085695000000],[17106204430399213440,2167765091684251776000,2359184985544305369600],[0,-18259895191104806400,70065325740009600000],[7843950397887706800,661363476934858812000,521270417207349612000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_20 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_0, 8832000, by norm_num, R7.Core.Certificates.Terminal005.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_1, 132480000, by norm_num, R7.Core.Certificates.Terminal005.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_2, 10368000, by norm_num, R7.Core.Certificates.Terminal005.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_3, 1866240000000, by norm_num, R7.Core.Certificates.Terminal005.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_4, 4199040000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_5, 8448636441600000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_6, 224386726950630604800000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_6⟩
theorem bound_20 : minorBindings polynomial_20 witness_20 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_20 witness_20 (by decide +kernel)
theorem positive_20 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_20 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_20 ρ hρ u
noncomputable def polynomial_21 : BiPoly := r7_rat_grid%[[289119636266031360,14606765652082620150,54562509753621422400],[0,5647255248712995000,45888335041756500000],[2255481024569502840,208106200242757520100,532225663878929655600],[0,36191756133843133500,193643646474638025000],[7093531037788468560,924604458794682608250,1676920401979769795400],[0,37041632998436646000,285445545748755975000],[11431264579330183200,1641590181880023384000,2289490595868575313000],[0,-9187596461910793500,169782429102694200000],[9843188151674376000,1254734910352994490000,1367979185360751840000],[0,-8529293148476587200,32727882418030800000],[4212491880347101800,355176682057609362000,279941520352095162000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_21 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_8, 1863000, by norm_num, R7.Core.Certificates.Terminal005.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_9, 2012040000, by norm_num, R7.Core.Certificates.Terminal005.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_10, 314928000, by norm_num, R7.Core.Certificates.Terminal005.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_11, 56687040000000, by norm_num, R7.Core.Certificates.Terminal005.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_12, 3188646000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_13, 1033121304000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_14, 13719297164101056000000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_14⟩
theorem bound_21 : minorBindings polynomial_21 witness_21 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_21 witness_21 (by decide +kernel)
theorem positive_21 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_21 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_21 ρ hρ u
noncomputable def polynomial_22 : BiPoly := r7_rat_grid%[[152590919140405440,9184611446914643100,31722524040110889600],[0,1462197930604020000,22296625347924000000],[1110064328706620520,110839443209884995300,276024873398377546800],[0,11169570017294929800,85611421683732870000],[3244328149066043760,435672129073342077000,789749459381685938400],[0,10727110993613850000,114244032236366250000],[4840265182238906400,702364367238072408000,983702462261825601000],[0,-3980407722135831000,61428741501364200000],[3849314855910107040,492543277384574466000,537611936988941193600],[0,-2823075901256335200,10832468124277800000],[1520370632676999960,128190204788608436400,101036364816733196400],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_22 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_16, 414000, by norm_num, R7.Core.Certificates.Terminal005.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_17, 447120000, by norm_num, R7.Core.Certificates.Terminal005.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_18, 11664000, by norm_num, R7.Core.Certificates.Terminal005.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_19, 2099520000000, by norm_num, R7.Core.Certificates.Terminal005.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_20, 18895680000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_21, 2040733440000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_22, 9033282083358720000000000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_22⟩
theorem bound_22 : minorBindings polynomial_22 witness_22 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_22 witness_22 (by decide +kernel)
theorem positive_22 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_22 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_22 ρ hρ u
noncomputable def polynomial_23 : BiPoly := r7_rat_grid%[[53005266648772416,3563198114537769840,11758513123583677440],[0,174640669837563600,7168243667377320000],[352109576876367528,36786214033072909920,90278599990656107520],[0,2342191956937795800,24801678775503270000],[934806415832588880,127515695159678796000,231087521274861499200],[0,2159292341841973200,29757027564441720000],[1266707696628479760,184748746448434183200,259278586168687538400],[0,-1022283336551664600,14420954623745970000],[917301363921995040,117580042148276646000,128406534770311113600],[0,-603514706347605600,2315755596983400000],[331189016799703176,27924235692805149840,22009195393199205840],[0,0,0],[44893243901194128,-189115344514118880,225456378437711520]]
noncomputable def witness_23 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal005.polynomial_24, 98366400, by norm_num, R7.Core.Certificates.Terminal005.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal005.polynomial_25, 127482854400, by norm_num, R7.Core.Certificates.Terminal005.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal005.polynomial_26, 544195584, by norm_num, R7.Core.Certificates.Terminal005.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal005.polynomial_27, 1057916215296000, by norm_num, R7.Core.Certificates.Terminal005.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal005.polynomial_28, 14281868906496000000, by norm_num, R7.Core.Certificates.Terminal005.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal005.polynomial_29, 2776395315422822400000000, by norm_num, R7.Core.Certificates.Terminal005.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal005.polynomial_30, 2457936109395067655946240000000000, by norm_num, R7.Core.Certificates.Terminal005.positive_30⟩
theorem bound_23 : minorBindings polynomial_23 witness_23 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_23 witness_23 (by decide +kernel)
theorem positive_23 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_23 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_23 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry003

namespace R7.Core.SpectralSliceCertificates.Entry004
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_24 : BiPoly := r7_rat_grid%[[9637321208867712,647854202643230880,2137911477015214080],[0,29400786167940000,1206775028178000000],[55149692763768408,5761696173854793120,14140021685283486720],[0,342759798576262800,3629513967146820000],[128306762957414160,17502154237602972000,31717895076941774400],[0,278928632131034400,3843892202088240000],[154476548369326800,22530334932735876000,31619339776669212000],[0,-118028988577659600,1664989174436220000],[100526176868163840,12885484071044016000,14071949015924505600],[0,-62925703979371200,241453190206800000],[32925223892368152,2776093606887061680,2188048664820973680],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
noncomputable def witness_24 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_0, 17884800, by norm_num, R7.Core.Certificates.Terminal006.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_1, 7726233600, by norm_num, R7.Core.Certificates.Terminal006.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_2, 544195584, by norm_num, R7.Core.Certificates.Terminal006.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_3, 1763193692160000, by norm_num, R7.Core.Certificates.Terminal006.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_4, 95212459376640000000, by norm_num, R7.Core.Certificates.Terminal006.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_5, 2056589122535424000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_6, 165517583124246980198400000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_6⟩
theorem bound_24 : minorBindings polynomial_24 witness_24 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_24 witness_24 (by decide +kernel)
theorem positive_24 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_24 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_24 ρ hρ u
noncomputable def polynomial_25 : BiPoly := r7_rat_grid%[[2538224515915776,4194477691966240,127195300246179840],[0,69397305403116800,658166307428160000],[23882488034452416,854795109583540240,3195596947805002440],[0,1287106409445280800,3944579412818520000],[92326559588403840,8693593407437493000,15810511524590595600],[0,2269898179753406400,8581268923061940000],[185371858043192160,23613194911286738700,31185001997066804400],[0,-63633145678727400,7684513686724680000],[201052353736327680,24383387513092707000,26172827190329011200],[0,-560610817270761600,2151128421842400000],[109427949995223564,9226428752301116760,7272044091905000760],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
noncomputable def witness_25 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_8, 73600, by norm_num, R7.Core.Certificates.Terminal006.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_9, 1177600, by norm_num, R7.Core.Certificates.Terminal006.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_10, 1024, by norm_num, R7.Core.Certificates.Terminal006.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_11, 18432000, by norm_num, R7.Core.Certificates.Terminal006.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_12, 995328000000, by norm_num, R7.Core.Certificates.Terminal006.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_13, 10749542400000000, by norm_num, R7.Core.Certificates.Terminal006.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_14, 4758272043909120000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_14⟩
theorem bound_25 : minorBindings polynomial_25 witness_25 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_25 witness_25 (by decide +kernel)
theorem positive_25 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_25 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_25 ρ hρ u
noncomputable def polynomial_26 : BiPoly := r7_rat_grid%[[23002659675486720,110921985328062800,1353932323416004800],[0,764612203749916000,5713739805409200000],[219970284527851200,8756518194060938000,31036364160643233000],[0,11511261360871258800,34434446236214220000],[860809393809529920,83321604635943421500,151556279958624817800],[0,19899094790817306000,75464634461260725000],[1750734214852370400,225043800718015525500,298597549304439486000],[0,-626879051693532000,68416737528531150000],[1928846018657893680,234751999952199132000,252265884169371451200],[0,-5085540985241908800,19513807826713200000],[1070069776501964940,90223042223829504600,71111581606681644600],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_26 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_16, 184000, by norm_num, R7.Core.Certificates.Terminal006.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_17, 73600000, by norm_num, R7.Core.Certificates.Terminal006.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_18, 16000000, by norm_num, R7.Core.Certificates.Terminal006.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_19, 1440000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_20, 311040000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_21, 16796160000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_22, 74348000686080000000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_22⟩
theorem bound_26 : minorBindings polynomial_26 witness_26 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_26 witness_26 (by decide +kernel)
theorem positive_26 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_26 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_26 ρ hρ u
noncomputable def polynomial_27 : BiPoly := r7_rat_grid%[[103908566120302080,1015069519982256700,7781760206395987200],[0,4070988147602694000,23973258805372800000],[989866280375330400,45749964624802198500,151499381542631923500],[0,48707523964364935200,142507222177916880000],[3861422580432654720,390151453478898944625,709672506255315424800],[0,80120540619701226000,307897063816905225000],[7835393814510853800,1022207972804792833500,1366340553812194204500],[0,-3077805611167389000,275846609131546050000],[8626402552499309520,1056245226078964698000,1137247598248141636800],[0,-20387928089316268800,78230833627003200000],[4793525243153598600,404166569237969274000,318554143848935874000],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
noncomputable def witness_27 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal006.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_25, 27600000, by norm_num, R7.Core.Certificates.Terminal006.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_26, 54000000, by norm_num, R7.Core.Certificates.Terminal006.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_27, 4860000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_28, 262440000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_29, 14030042400000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_30, 279467164453910400000000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_30⟩
theorem bound_27 : minorBindings polynomial_27 witness_27 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_27 witness_27 (by decide +kernel)
theorem positive_27 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_27 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_27 ρ hρ u
noncomputable def polynomial_28 : BiPoly := r7_rat_grid%[[301017563684386560,4754281717097516900,28539847539347390400],[0,12921809047538685000,63858193536784500000],[2831331805137056160,153452985579265602400,475544154015643154400],[0,126156000417191349600,368093200049296740000],[10892497416146614800,1158868557845595495000,2107505330638879707000],[0,193682134133048304000,769266899564760900000],[21789775350540041400,2896537582609072308000,3906564474485530251000],[0,-9852608796252223500,665890686987088950000],[23648783108235543360,2918823591389217084000,3150637863110351942400],[0,-47709124653450528000,183065418756792000000],[12957043990584878640,1092474484122026037600,861061503979547877600],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_28 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal007.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_1, 180320000, by norm_num, R7.Core.Certificates.Terminal007.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_2, 1024000, by norm_num, R7.Core.Certificates.Terminal007.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_3, 184320000000, by norm_num, R7.Core.Certificates.Terminal007.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_4, 1244160000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_5, 806215680000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_6, 42824448395182080000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_6⟩
theorem bound_28 : minorBindings polynomial_28 witness_28 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_28 witness_28 (by decide +kernel)
theorem positive_28 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_28 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_28 ρ hρ u
noncomputable def polynomial_29 : BiPoly := r7_rat_grid%[[616312640270799360,14187689523640518275,72214923452899292400],[0,26300707165213301000,119292564646658700000],[5669079410239507980,358489289379268500950,1046534991822073393200],[0,217513365222820959600,657232992132618240000],[21303335317381666920,2394365714566696514625,4352387687468253397800],[0,307693982272188942000,1305253947191955075000],[41562773541813871800,5640498162683623768500,7679835553872411949500],[0,-22072481476063263000,1069150804706687850000],[43921562109981917760,5469725108995832034000,5920763680855351238400],[0,-72559057206758572800,278417478598459200000],[23386592852961496200,1971842959009486458000,1554158095747838658000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_29 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal007.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_9, 230000, by norm_num, R7.Core.Certificates.Terminal007.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_10, 2000, by norm_num, R7.Core.Certificates.Terminal007.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_11, 180000000, by norm_num, R7.Core.Certificates.Terminal007.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_12, 158760000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_13, 257191200000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_14, 23907528970617600000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_14⟩
theorem bound_29 : minorBindings polynomial_29 witness_29 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_29 witness_29 (by decide +kernel)
theorem positive_29 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_29 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_29 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry004

namespace R7.Core.SpectralSliceCertificates.Entry005
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_30 : BiPoly := r7_rat_grid%[[928127573087343264,29242889922407080860,130605245633298533760],[0,35234593964156248200,163487871668972340000],[8281174165130472444,603405256587171837660,1672227395086797647460],[0,256097849093337849300,848941296115664295000],[30105247143436446240,3570449371141668348000,6485987650542633786600],[0,330984755864803447200,1576029701454015870000],[56674012784520017880,7851758614483720949100,10788154553354352289200],[0,-34965057121485365700,1198527897427322490000],[57614065117566400800,7238649554545728060000,7857103508332756272000],[0,-75682460331552816000,290402336948724000000],[29406098491636803048,2479378190198015146320,1954184875175108434320],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
noncomputable def witness_30 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_16, 82800, by norm_num, R7.Core.Certificates.Terminal007.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_17, 292118400, by norm_num, R7.Core.Certificates.Terminal007.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_18, 31104, by norm_num, R7.Core.Certificates.Terminal007.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_19, 38631168000, by norm_num, R7.Core.Certificates.Terminal007.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_20, 793618560000000, by norm_num, R7.Core.Certificates.Terminal007.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_21, 1079956136448000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_22, 120466404538538552524800000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_22⟩
theorem bound_30 : minorBindings polynomial_30 witness_30 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_30 witness_30 (by decide +kernel)
theorem positive_30 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_30 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_30 ρ hρ u
noncomputable def polynomial_31 : BiPoly := r7_rat_grid%[[1042704614126103840,42732487904322477850,171164259842470245600],[0,30646069184327712000,166933294569824400000],[8932364768148814800,737277550493224662000,1955196999877958082000],[0,204398487730460610600,806631558448686390000],[31087914018467435640,3871974097317080232375,7028470639187517207600],[0,240558222413553138000,1379363785249862925000],[55826108174581713000,7880971989813367770000,10914948458695289857500],[0,-38756778474440754000,959049876258926550000],[53919728117661379680,6827271627113851032000,7428263355697626691200],[0,-55740732688635724800,213883625943187200000],[26030294653731056640,2194746945680124057600,1729845532658463897600],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_31 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal007.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_25, 165600000, by norm_num, R7.Core.Certificates.Terminal007.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_26, 144000000, by norm_num, R7.Core.Certificates.Terminal007.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_27, 64800000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_28, 97977600000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_29, 28443289190400000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_30, 2643981443918541619200000000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_30⟩
theorem bound_31 : minorBindings polynomial_31 witness_31 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_31 witness_31 (by decide +kernel)
theorem positive_31 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_31 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_31 ρ hρ u
noncomputable def polynomial_32 : BiPoly := r7_rat_grid%[[864681875128964160,44008346148115200900,161083974140109374400],[0,16132934374693983000,126125872794197100000],[7035121064096098200,644058682529982445500,1648452861256245025500],[0,107121763548456605400,560677122451911510000],[23150205945030583440,3003994860656162598000,5449048524074393634600],[0,115670522721826296000,873363193556399100000],[39142640950694418600,5611000282880709357000,7820279883250291899000],[0,-29320115699911180500,550308381725048850000],[35443854527433433920,4514838610300587108000,4921237242215861932800],[0,-29311937017299820800,112473286056331200000],[15978417477178662000,1347221897459897580000,1061847146163119580000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_32 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_0, 138000, by norm_num, R7.Core.Certificates.Terminal008.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_1, 82800000, by norm_num, R7.Core.Certificates.Terminal008.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_2, 162000000, by norm_num, R7.Core.Certificates.Terminal008.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_3, 29160000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_4, 65610000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_5, 1062882000000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_6, 56458013020992000000000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_6⟩
theorem bound_32 : minorBindings polynomial_32 witness_32 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_32 witness_32 (by decide +kernel)
theorem positive_32 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_32 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_32 ρ hρ u
noncomputable def polynomial_33 : BiPoly := r7_rat_grid%[[511313430803814720,30671600011258389675,104880413390838274800],[0,4265008730013615000,68163774402325500000],[3885225150473171820,384551024451129016050,959138449497298851300],[0,35498992425417955200,275988552090217380000],[11898924802836384600,1590982474552119886875,2884389377205673989000],[0,36271732072260186000,389451518885083725000],[18648752200363729800,2701731665441749221000,3781666265582993044500],[0,-14413407241027950000,221841597464583750000],[15606688958782436160,1995753627890999379000,2177968443861111494400],[0,-10811780047364688000,41486048135532000000],[6493047829362601740,547461989240522016600,431496067577194956600],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
noncomputable def witness_33 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_8, 34500, by norm_num, R7.Core.Certificates.Terminal008.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_9, 6210000, by norm_num, R7.Core.Certificates.Terminal008.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_10, 486000, by norm_num, R7.Core.Certificates.Terminal008.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_11, 43740000000, by norm_num, R7.Core.Certificates.Terminal008.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_12, 42515280000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_13, 20662426080000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_14, 411578914923031680000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_14⟩
theorem bound_33 : minorBindings polynomial_33 witness_33 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_33 witness_33 (by decide +kernel)
theorem positive_33 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_33 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_33 ρ hρ u
noncomputable def polynomial_34 : BiPoly := r7_rat_grid%[[196761974681049120,13113008982819726300,43072946570540620800],[0,357658043412087000,24172768471311900000],[1368136608947331660,141690169244186087400,348346813264171574400],[0,7786894859456501700,88522146930146355000],[3812543813591735040,517997403358817485500,938844942223235403600],[0,7801414648820442000,112582966643261325000],[5432425284321325800,791184792003543486000,1109772457988534622000],[0,-4151787836157157500,57855459146454000000],[4140421909757498160,530443359050326344000,579194185925086574400],[0,-2568512826067060800,9855680218441200000],[1573632024267595500,132680944446808095000,104575855303943595000],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
noncomputable def witness_34 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_16, 414000, by norm_num, R7.Core.Certificates.Terminal008.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_17, 149040000, by norm_num, R7.Core.Certificates.Terminal008.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_18, 11664000, by norm_num, R7.Core.Certificates.Terminal008.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_19, 2099520000000, by norm_num, R7.Core.Certificates.Terminal008.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_20, 14171760000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_21, 19131876000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_22, 84687019531488000000000000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_22⟩
theorem bound_34 : minorBindings polynomial_34 witness_34 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_34 witness_34 (by decide +kernel)
theorem positive_34 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_34 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_34 ρ hρ u
noncomputable def polynomial_35 : BiPoly := r7_rat_grid%[[39352394936209824,2622601796563945260,8614589314108124160],[0,67380798059269200,4491590815220040000],[236153812603828824,24464509053509605860,60142548997628084160],[0,1268293526803823400,14363307520975710000],[577380433308363720,78464464315954276500,142212005796416734800],[0,1123546601858896800,16159811612829030000],[731188995614813520,106502087040241293900,149393084423192686800],[0,-532342557121375800,7425761565976560000],[500536588989399120,64128137645317878000,70022777900868100800],[0,-297466964266118400,1141415080977600000],[172373230965927384,14533666530173440560,11455078304062744560],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
noncomputable def witness_35 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal008.polynomial_24, 82800, by norm_num, R7.Core.Certificates.Terminal008.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal008.polynomial_25, 5961600, by norm_num, R7.Core.Certificates.Terminal008.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal008.polynomial_26, 93312, by norm_num, R7.Core.Certificates.Terminal008.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal008.polynomial_27, 5038848000, by norm_num, R7.Core.Certificates.Terminal008.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal008.polynomial_28, 90699264000000, by norm_num, R7.Core.Certificates.Terminal008.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal008.polynomial_29, 1959104102400000000, by norm_num, R7.Core.Certificates.Terminal008.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal008.polynomial_30, 867195080002437120000000000, by norm_num, R7.Core.Certificates.Terminal008.positive_30⟩
theorem bound_35 : minorBindings polynomial_35 witness_35 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_35 witness_35 (by decide +kernel)
theorem positive_35 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_35 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_35 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry005

namespace R7.Core.SpectralSliceCertificates.Entry006
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_36 : BiPoly := r7_rat_grid%[[6874358063938560,59966397912154400,478637214790070400],[0,278417117822888000,1615272178845600000],[67038562903726080,2988361764095491200,10038919614412147200],[0,3383819542429903200,9807699448081080000],[266117730578340480,26569091732503971000,48335814890447893200],[0,5699735928033516000,21705526563967350000],[549249949757606400,71318550774387888000,95115026212736976000],[0,-205808882199930000,19996112729938500000],[615722833317503520,75223374924490398000,80934498811817596800],[0,-1521657932592067200,5838777145000800000],[348620017683898080,29393932308215947200,23167574098104427200],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
noncomputable def witness_36 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal009.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_1, 235520000, by norm_num, R7.Core.Certificates.Terminal009.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_2, 393216000, by norm_num, R7.Core.Certificates.Terminal009.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_3, 35389440000000, by norm_num, R7.Core.Certificates.Terminal009.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_4, 7644119040000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_5, 29720334827520000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_6, 43852235156666449920000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_6⟩
theorem bound_36 : minorBindings polynomial_36 witness_36 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_36 witness_36 (by decide +kernel)
theorem positive_36 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_36 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_36 ρ hρ u
noncomputable def polynomial_37 : BiPoly := r7_rat_grid%[[60282832252999680,815397572011553200,4923509615908771200],[0,2648895862150700000,12964791515490000000],[586587425407603200,28983733790820498000,92900857490282538000],[0,27940567184504917200,78613305453720180000],[2335318860177273600,240385747710307612500,437340651628237749000],[0,45439969708111230000,173384061960342375000],[4840265182238906400,635502747970003968000,852222318922652976000],[0,-1832541844374621000,159074614793448450000],[5453545095097888320,669435790768904268000,721353722828144428800],[0,-12098896719670008000,46424863389762000000],[3108528491014757880,262095896414925529200,206577535708097809200],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_37 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_8, 184000, by norm_num, R7.Core.Certificates.Terminal009.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_9, 3385600000, by norm_num, R7.Core.Certificates.Terminal009.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_10, 26496000000, by norm_num, R7.Core.Certificates.Terminal009.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_11, 9538560000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_12, 128770560000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_13, 41721661440000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_14, 554041301112668160000000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_14⟩
theorem bound_37 : minorBindings polynomial_37 witness_37 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_37 witness_37 (by decide +kernel)
theorem positive_37 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_37 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_37 ρ hρ u
noncomputable def polynomial_38 : BiPoly := r7_rat_grid%[[256202037075248640,4948992873327868600,25273595867226777600],[0,11755127329837168000,49846885296906600000],[2467857096893416320,138951307793899849800,421942702032125668800],[0,106223327658098463000,294991287990273450000],[9722801370772939680,1044623477827346211000,1900118126283555571200],[0,163001579035427532000,634010989014940950000],[19944638800573082400,2660199241786164108000,3594192419838237066000],[0,-8002289208060513000,565761838195281600000],[22241416632081249600,2748787416424432620000,2968347905837424864000],[0,-41908518850261219200,160807824677728800000],[12550320636620330880,1058181563095774099200,834032667531759379200],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_38 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_16, 1748000, by norm_num, R7.Core.Certificates.Terminal009.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_17, 7360000, by norm_num, R7.Core.Certificates.Terminal009.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_18, 1152000, by norm_num, R7.Core.Certificates.Terminal009.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_19, 414720000000, by norm_num, R7.Core.Certificates.Terminal009.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_20, 83980800000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_21, 11754624614400000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_22, 624380457601754726400000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_22⟩
theorem bound_38 : minorBindings polynomial_38 witness_38 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_38 witness_38 (by decide +kernel)
theorem positive_38 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_38 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_38 ρ hρ u
noncomputable def polynomial_39 : BiPoly := r7_rat_grid%[[687964603168005120,17966772019989658800,81765613053081160800],[0,30491203187374317000,119769672025737900000],[6491218348662351840,418571937063467247600,1206843152745552690600],[0,239522741381205667200,680163801799770180000],[25042221544831182720,2825138837170234569000,5136434700677845444800],[0,341222955441730956000,1395672900067328850000],[50239206341891060400,6825678084474752448000,9300083452807038336000],[0,-22350227798949151500,1184214261737011050000],[54711371760498169920,6816073267098902268000,7379029001866608172800],[0,-83370837254123260800,319903526733991200000],[30097528193376534240,2537676155942643441600,2000133897136348881600],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
noncomputable def witness_39 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal009.polynomial_24, 552000, by norm_num, R7.Core.Certificates.Terminal009.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal009.polynomial_25, 99360000, by norm_num, R7.Core.Certificates.Terminal009.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal009.polynomial_26, 3456000, by norm_num, R7.Core.Certificates.Terminal009.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal009.polynomial_27, 3732480000000, by norm_num, R7.Core.Certificates.Terminal009.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal009.polynomial_28, 88179840000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal009.polynomial_29, 799967508480000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal009.polynomial_30, 99149304146945310720000000000000000, by norm_num, R7.Core.Certificates.Terminal009.positive_30⟩
theorem bound_39 : minorBindings polynomial_39 witness_39 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_39 witness_39 (by decide +kernel)
theorem positive_39 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_39 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_39 ρ hρ u
noncomputable def polynomial_40 : BiPoly := r7_rat_grid%[[1278134852916807360,43432341661086843900,179910835614742262400],[0,49428110449290114000,198264463611301800000],[11717083822516873920,860009421110813293800,2366660357931281977800],[0,345556600168431694800,1063059666378742620000],[43813704627029378160,5194517260829946004500,9438080824038599159400],[0,452097882351034110000,2044086534020302875000],[84996429724989590400,11770743496685473368000,16172623802017163286000],[0,-42755820286951075500,1614592219486094100000],[89250490696118129280,11210502262747308192000,12167311276246285555200],[0,-105955444464173942400,406563271728213600000],[47179909059887540160,3977978839045224854400,3135345027943465814400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_40 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_0, 138000, by norm_num, R7.Core.Certificates.Terminal010.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_1, 33120000, by norm_num, R7.Core.Certificates.Terminal010.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_2, 3456000, by norm_num, R7.Core.Certificates.Terminal010.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_3, 1244160000000, by norm_num, R7.Core.Certificates.Terminal010.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_4, 9797760000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_5, 177770557440000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_6, 33049768048981770240000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_6⟩
theorem bound_40 : minorBindings polynomial_40 witness_40 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_40 witness_40 (by decide +kernel)
theorem positive_40 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_40 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_40 ρ hρ u
noncomputable def polynomial_41 : BiPoly := r7_rat_grid%[[1705567895421217920,72806876653506075800,277962874661041312800],[0,50107029609616551000,235119665623808700000],[15030517167910803960,1239717105015116834400,3276949132772683331400],[0,322591661702940846900,1173129906861129735000],[53894950287969062160,6692975028617223184500,12151604684369940719400],[0,385680871512836190000,2078634975988458375000],[99911998673094589200,14085110822061766059000,19498883257432086228000],[0,-56308207722561144000,1502246783457337050000],[99864379537115094720,12636611768770640028000,13746284309861082604800],[0,-90818952397863379200,348482804338468800000],[50026972537639374480,4218029286228988423200,3324546883077985303200],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_41 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_8, 92000, by norm_num, R7.Core.Certificates.Terminal010.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_9, 11040000, by norm_num, R7.Core.Certificates.Terminal010.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_10, 3456000, by norm_num, R7.Core.Certificates.Terminal010.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_11, 622080000000, by norm_num, R7.Core.Certificates.Terminal010.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_12, 3605575680000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_13, 2133246689280000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_14, 396597216587781242880000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_14⟩
theorem bound_41 : minorBindings polynomial_41 witness_41 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_41 witness_41 (by decide +kernel)
theorem positive_41 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_41 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_41 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry006

namespace R7.Core.SpectralSliceCertificates.Entry007
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_42 : BiPoly := r7_rat_grid%[[1636559916394757760,84767642942896747400,301493745839527298400],[0,29563811920261125000,201068508437212500000],[13716718456629578400,1248490006200168351000,3193372712255033556000],[0,189185545763372586900,922188052629435735000],[46570602851209584000,6016455635775512145000,10915591194785550060000],[0,208174748231261214000,1487382039929084400000],[81414862344278532000,11648520307733070060000,16224150851683704630000],[0,-49933458897783552000,974190795992051400000],[76408271601210198720,9724971004133827428000,10597738388187177964800],[0,-54058900236823440000,207430240677660000000],[35791655148880202880,3017777050310170579200,2378537607405387859200],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
noncomputable def witness_42 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_16, 644000, by norm_num, R7.Core.Certificates.Terminal010.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_17, 55200000, by norm_num, R7.Core.Certificates.Terminal010.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_18, 144000000, by norm_num, R7.Core.Certificates.Terminal010.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_19, 259200000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_20, 261273600000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_21, 9481096396800000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_22, 1175102863963796275200000000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_22⟩
theorem bound_42 : minorBindings polynomial_42 witness_42 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_42 witness_42 (by decide +kernel)
theorem positive_42 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_42 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_42 ρ hρ u
noncomputable def polynomial_43 : BiPoly := r7_rat_grid%[[1099368493456020480,66124616489149655200,222562792274697643200],[0,7995613580852466000,121054031265994200000],[8614979071901486640,845342274228196734600,2110404368570563947600],[0,66150312110600173500,505628226921764025000],[27259416718476233760,3626304594324317187000,6575589266864785538400],[0,69644155910749866000,739493152033008600000],[44231785016417240400,6394734652789359918000,8944096068951880536000],[0,-28401937729236139500,438569402200050150000],[38409376745044267200,4907541121432609860000,5354230780482082848000],[0,-22344345431220355200,85737832813432800000],[16617554176265808480,1401110773358293483200,1104321032009644363200],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
noncomputable def witness_43 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal010.polynomial_24, 368000, by norm_num, R7.Core.Certificates.Terminal010.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal010.polynomial_25, 44160000, by norm_num, R7.Core.Certificates.Terminal010.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal010.polynomial_26, 1152000, by norm_num, R7.Core.Certificates.Terminal010.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal010.polynomial_27, 414720000000, by norm_num, R7.Core.Certificates.Terminal010.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal010.polynomial_28, 2332800000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal010.polynomial_29, 3023308800000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal010.polynomial_30, 160591681481932800000000000000000, by norm_num, R7.Core.Certificates.Terminal010.positive_30⟩
theorem bound_43 : minorBindings polynomial_43 witness_43 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_43 witness_43 (by decide +kernel)
theorem positive_43 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_43 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_43 ρ hρ u
noncomputable def polynomial_44 : BiPoly := r7_rat_grid%[[473834959435995840,31428967450527224100,102316291526124525600],[0,199965781339449000,47440038435666300000],[3403254544909469280,349041897749040004200,859517578239597160200],[0,14463711253102248900,180160343767756035000],[9810375828029587440,1325968527736014280500,2403684844776076494600],[0,15546955138871508000,238630652037502425000],[14486467424856868800,2105463028335113736000,2951050695936337242000],[0,-9350625373079737500,128177059656060000000],[11464172753673517920,1467508631262962418000,1601985218272006492800],[0,-5972221359496684800,22916102779627200000],[4532060229890675040,382121120006807313600,301178463275357553600],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
noncomputable def witness_44 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_0, 1242000, by norm_num, R7.Core.Certificates.Terminal011.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_1, 33120000, by norm_num, R7.Core.Certificates.Terminal011.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_2, 10368000, by norm_num, R7.Core.Certificates.Terminal011.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_3, 3732480000000, by norm_num, R7.Core.Certificates.Terminal011.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_4, 4199040000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_5, 16325867520000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_6, 216798770000609280000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_6⟩
theorem bound_44 : minorBindings polynomial_44 witness_44 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_44 witness_44 (by decide +kernel)
theorem positive_44 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_44 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_44 ρ hρ u
noncomputable def polynomial_45 : BiPoly := r7_rat_grid%[[105296657652443520,6984214989006049800,22736953672472116800],[0,44143966891038000,9830970566175600000],[652840380152301240,66983549404668738600,164936663002841511600],[0,2651523079756605600,32810992182170640000],[1651694996166077520,223329786079240059000,404841501233419726800],[0,2532948111199638000,38630651516659800000],[2168393030813883600,315218318018326767000,441847697574521124000],[0,-1355087552953752000,18612963871578900000],[1541401378645178880,197330741421964632000,215419472316794419200],[0,-783711040470350400,3007189732575600000],[551981694666171960,46540392821341916400,36681992321998676400],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
noncomputable def witness_45 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_8, 276000, by norm_num, R7.Core.Certificates.Terminal011.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_9, 198720000, by norm_num, R7.Core.Certificates.Terminal011.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_10, 3456000, by norm_num, R7.Core.Certificates.Terminal011.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_11, 622080000000, by norm_num, R7.Core.Certificates.Terminal011.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_12, 89579520000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_13, 29023764480000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_14, 42824448395182080000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_14⟩
theorem bound_45 : minorBindings polynomial_45 witness_45 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_45 witness_45 (by decide +kernel)
theorem positive_45 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_45 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_45 ρ hρ u
noncomputable def polynomial_46 : BiPoly := r7_rat_grid%[[14674110482638080,272774390703429200,1384821074676727200],[0,698009415973852000,2848033355342400000],[142456946170417920,7768052926195393800,23862859612713937800],[0,6356689621785176400,17239328968677660000],[568894536287370720,60412417457019871500,109914742310611114800],[0,9895579015980204000,37854596211244650000],[1184320204164838800,157284634742629236000,212102350482668292000],[0,-453200937237468000,34546053754362600000],[1341396172584561240,165465301804348738500,178574239087482621600],[0,-2625718011502852800,10075183118629200000],[769869205718608260,64911600513976883400,51161726133313943400],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
noncomputable def witness_46 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_16, 184000, by norm_num, R7.Core.Certificates.Terminal011.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_17, 14720000, by norm_num, R7.Core.Certificates.Terminal011.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_18, 1152000, by norm_num, R7.Core.Certificates.Terminal011.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_19, 414720000000, by norm_num, R7.Core.Certificates.Terminal011.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_20, 515082240000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_21, 3627970560000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_22, 12044376111144960000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_22⟩
theorem bound_46 : minorBindings polynomial_46 witness_46 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_46 witness_46 (by decide +kernel)
theorem positive_46 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_46 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_46 ρ hρ u
noncomputable def polynomial_47 : BiPoly := r7_rat_grid%[[119772469344775680,2802363472808723200,12679954682945611200],[0,5811577866525547000,20663564735651400000],[1163747552906869920,69499790283145346300,205545810278083492800],[0,47179250024168864100,123362721415614915000],[4631263158177139680,507199854154128621000,922661597543015446200],[0,70147949321549142000,267013784616337575000],[9603292090293149400,1290319375101236163000,1749611799003353346000],[0,-3370605772848426000,239339622487036950000],[10831695557544653760,1343083274774478774000,1451864192309545478400],[0,-17796533189074891200,68287352248486800000],[6188005313889190920,521742298470833062800,411224440241353582800],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_47 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal011.polynomial_24, 736000, by norm_num, R7.Core.Certificates.Terminal011.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal011.polynomial_25, 11040000, by norm_num, R7.Core.Certificates.Terminal011.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal011.polynomial_26, 16000, by norm_num, R7.Core.Certificates.Terminal011.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal011.polynomial_27, 25920000000, by norm_num, R7.Core.Certificates.Terminal011.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal011.polynomial_28, 2799360000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal011.polynomial_29, 2720977920000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal011.polynomial_30, 72266256666869760000000000000000, by norm_num, R7.Core.Certificates.Terminal011.positive_30⟩
theorem bound_47 : minorBindings polynomial_47 witness_47 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_47 witness_47 (by decide +kernel)
theorem positive_47 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_47 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_47 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry007

namespace R7.Core.SpectralSliceCertificates.Entry008
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_48 : BiPoly := r7_rat_grid%[[470563029395948160,13950068950801729650,57815272108504184400],[0,21629634581764659000,70367146801143300000],[4496297363503815600,299860270236319327750,850385239438496904000],[0,156049263327568192800,405754385609438820000],[17591943396280168440,2005433156347393285500,3646575669788434097100],[0,217182270442651398000,844469847653427675000],[35821395160753892400,4886645126756589783000,6671588356392834028500],[0,-12103940986708032000,725006290672506150000],[39626162344219333680,4945904001120579147000,5357500792483285051200],[0,-51416020669689849600,197289206688974400000],[22166422791067852920,1868964195930730642800,1473071586404473162800],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_48 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal012.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_1, 158700000, by norm_num, R7.Core.Certificates.Terminal012.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_2, 5750000, by norm_num, R7.Core.Certificates.Terminal012.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_3, 517500000000, by norm_num, R7.Core.Certificates.Terminal012.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_4, 391230000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_5, 887309640000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_6, 82480974948630720000000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_6⟩
theorem bound_48 : minorBindings polynomial_48 witness_48 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_48 witness_48 (by decide +kernel)
theorem positive_48 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_48 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_48 ρ hρ u
noncomputable def polynomial_49 : BiPoly := r7_rat_grid%[[1143589123694240640,42118453705510960475,162874461178452057600],[0,45322859137539224000,146757317791708800000],[10650489811943138280,795065742180695351700,2166358013438647682700],[0,293295460229845752300,800816464007498745000],[40502168173557069840,4822557137692682678625,8763537073932966473100],[0,376704923641376796000,1566982893711486600000],[79984523933451432000,11094655511111601555000,15257188293850082880000],[0,-27771455337152782500,1257170300976429000000],[85585473831132989280,10757986659373548042000,11678800349957397955200],[0,-83250706364708097600,319442570643596400000],[46163100674976170760,3892246536479595008400,3067772936823994568400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_49 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal012.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal012.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal012.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_11, 129600000000, by norm_num, R7.Core.Certificates.Terminal012.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_12, 6123600000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_13, 13888324800000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_14, 2582013128826700800000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_14⟩
theorem bound_49 : minorBindings polynomial_49 witness_49 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_49 witness_49 (by decide +kernel)
theorem positive_49 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_49 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_49 ρ hρ u
noncomputable def polynomial_50 : BiPoly := r7_rat_grid%[[1880492215819827600,84094828496922445875,306411282377739234000],[0,56047734403427245000,205355684597206500000],[16867661847797875500,1399186109398356120000,3679164540666022545000],[0,332141028127112460000,1041369565133799000000],[61640707370791052700,7655886197768288878125,13902088254651105993000],[0,390460498479153450000,1876347890545010625000],[116586883866516921000,16434551097575699107500,22753985458676985765000],[0,-43605812001912300000,1377605302555860000000],[119039747774717347200,15062140973979061830000,16384516931679882048000],[0,-84091622590614240000,322669263276360000000],[61008503094682164000,5143938153937790760000,4054325467168274760000],[0,0,0],[11784476524063458600,-49642777934956206000,59182299339899274000]]
noncomputable def witness_50 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_16, 517500, by norm_num, R7.Core.Certificates.Terminal012.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_17, 57500000, by norm_num, R7.Core.Certificates.Terminal012.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_18, 750000000, by norm_num, R7.Core.Certificates.Terminal012.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_19, 337500000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_20, 136930500000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_21, 4050761400000000000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_22, 941358953218068000000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_22⟩
theorem bound_50 : minorBindings polynomial_50 witness_50 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_50 witness_50 (by decide +kernel)
theorem positive_50 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_50 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_50 ρ hρ u
noncomputable def polynomial_51 : BiPoly := r7_rat_grid%[[2140734590747559360,113381107329993229525,391669422862708442400],[0,38647490736522329000,198960935517672300000],[18296290284990366240,1662547424103845381100,4244136037402529924100],[0,222150346207612431300,923817177673082595000],[63414090130238169840,8171813987768247567375,14828565041506329848100],[0,239945852947951827000,1509628523288591700000],[113308548228901207800,16192928490280913128500,22545520603211844252000],[0,-46243975744842687000,1003084343923602150000],[108836340822598717440,13844919608529122106000,15084990734876184729600],[0,-56341387135711540800,216188406395161200000],[52263950984444387160,4406640351873374084400,3473205483540822044400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_51 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal012.polynomial_24, 11500, by norm_num, R7.Core.Certificates.Terminal012.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal012.polynomial_25, 460000, by norm_num, R7.Core.Certificates.Terminal012.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal012.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal012.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal012.polynomial_27, 4320000000, by norm_num, R7.Core.Certificates.Terminal012.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal012.polynomial_28, 544320000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal012.polynomial_29, 28393908480000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal012.polynomial_30, 5278782396712366080000000000000000, by norm_num, R7.Core.Certificates.Terminal012.positive_30⟩
theorem bound_51 : minorBindings polynomial_51 witness_51 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_51 witness_51 (by decide +kernel)
theorem positive_51 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_51 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_51 ρ hρ u
noncomputable def polynomial_52 : BiPoly := r7_rat_grid%[[1664073873549704160,100691011371652527775,333390742148390474400],[0,11431796433187654000,132615533142649800000],[13311606515957452440,1298285116795170887850,3241599550300538994600],[0,81149062532729551200,558824149649199780000],[43056762612756802560,5704813654642539553875,10346345204058360792900],[0,84169107142300818000,827526509860481550000],[71505477834068383200,10319740303055400391500,14425038982632041500500],[0,-31345588781129448000,499072433217967350000],[63639352843601970960,8124939878382078129000,8862431570924907326400],[0,-25948272113675251200,99566515525276800000],[28267273100536069320,2383358011324509718800,1878504133121300638800],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_52 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_0, 11500, by norm_num, R7.Core.Certificates.Terminal013.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_1, 230000, by norm_num, R7.Core.Certificates.Terminal013.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_2, 6000, by norm_num, R7.Core.Certificates.Terminal013.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_3, 540000000, by norm_num, R7.Core.Certificates.Terminal013.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_4, 408240000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_5, 925888320000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_6, 86067104294223360000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_6⟩
theorem bound_52 : minorBindings polynomial_52 witness_52 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_52 witness_52 (by decide +kernel)
theorem positive_52 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_52 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_52 ρ hρ u
noncomputable def polynomial_53 : BiPoly := r7_rat_grid%[[814710579971872320,53911979081418386800,173857943880703708800],[0,-246115982977242000,57091539737627100000],[5982406130998524600,608642141887168731500,1500426801021137589000],[0,16297380029974187100,220581547566547365000],[17645234829572004480,2373872353463652711000,4304037483529877653200],[0,18373714225150149000,298458435902163525000],[26690114746033686000,3871534182784769497500,5422582870280955990000],[0,-12180234657825076500,164490356667102300000],[21667579705792147680,2771315027962210422000,3024506235586551811200],[0,-7911477145770033600,30357251096000400000],[8802655446518426520,742196790782452666800,584981245977136786800],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_53 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_8, 184000, by norm_num, R7.Core.Certificates.Terminal013.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_9, 36800000, by norm_num, R7.Core.Certificates.Terminal013.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_10, 2000000, by norm_num, R7.Core.Certificates.Terminal013.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_11, 900000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_12, 4050000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_13, 3936600000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_14, 104551875964800000000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_14⟩
theorem bound_53 : minorBindings polynomial_53 witness_53 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_53 witness_53 (by decide +kernel)
theorem positive_53 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_53 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_53 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry008

namespace R7.Core.SpectralSliceCertificates.Entry009
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_54 : BiPoly := r7_rat_grid%[[203677644992968080,13477994770354596700,43464485970175927200],[0,-54399567254992000,13398269027889600000],[1289575793044527660,131251613463039882400,323545879149589589400],[0,3423497713485765600,46016804820824640000],[3337163862475707180,449142807307181121000,814322595459260896200],[0,3464985055942044000,55884793248414900000],[4488401933175439800,651216397148201826000,912188418161706882000],[0,-2057728805681724000,27854543853474300000],[3274430781945295080,418854415353291499500,457137978554122927200],[0,-1218470449782369600,4675411774004400000],[1205644227823480860,101654015899246817400,80121193755944477400],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
noncomputable def witness_54 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal013.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal013.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal013.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_19, 2880000000, by norm_num, R7.Core.Certificates.Terminal013.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_20, 51840000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_21, 8398080000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_22, 27880500257280000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_22⟩
theorem bound_54 : minorBindings polynomial_54 witness_54 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_54 witness_54 (by decide +kernel)
theorem positive_54 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_54 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_54 ρ hρ u
noncomputable def polynomial_55 : BiPoly := r7_rat_grid%[[24430410965689344,684506363998002560,2856268153695480960],[0,1207816081052055600,3708572525712720000],[237567907290079296,15371031431345508440,44037748730891096640],[0,8700996614811263400,21762162216361710000],[942274005211062720,106220073730419654000,193201051320228394800],[0,12226253303051330400,46238159908543590000],[1946404509453517680,264472334452287687600,360480958829072071200],[0,-623120809559421600,40462162987834620000],[2186444346882563520,272488827022833528000,295026894383845996800],[0,-2917464457225392000,11194647909588000000],[1243411396405903152,104838358565970211680,82631014283239123680],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
noncomputable def witness_55 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_24, 294400, by norm_num, R7.Core.Certificates.Terminal013.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_25, 588800, by norm_num, R7.Core.Certificates.Terminal013.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_26, 1024, by norm_num, R7.Core.Certificates.Terminal013.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_27, 73728000, by norm_num, R7.Core.Certificates.Terminal013.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_28, 47775744000000, by norm_num, R7.Core.Certificates.Terminal013.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_29, 6191736422400000000, by norm_num, R7.Core.Certificates.Terminal013.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_30, 32889176367499837440000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_30⟩
theorem bound_55 : minorBindings polynomial_55 witness_55 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_55 witness_55 (by decide +kernel)
theorem positive_55 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_55 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_55 ρ hρ u
noncomputable def polynomial_56 : BiPoly := r7_rat_grid%[[185766306758585856,6223173637460030440,24103809982740287040],[0,8657280538057561800,23097834566237160000],[1782387791202817152,124733041005588165280,346785400194903688680],[0,56278971062078615700,132755811196900455000],[6996452375868308640,811906103531736790500,1476271750855371402600],[0,74542093957491879600,274269183660388035000],[14283931505883751440,1962683764574528530800,2688524507454657969600],[0,-3350586513382693200,232018987589532990000],[15832872856735804800,1982841032055189600000,2150103989733037632000],[0,-15977408292216705600,61307160022508400000],[8866569116427141168,747585678372292257120,589228634561789265120],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_56 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_0, 18400, by norm_num, R7.Core.Certificates.Terminal014.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_1, 147200, by norm_num, R7.Core.Certificates.Terminal014.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_2, 1024, by norm_num, R7.Core.Certificates.Terminal014.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_3, 73728000, by norm_num, R7.Core.Certificates.Terminal014.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_4, 1254113280000000, by norm_num, R7.Core.Certificates.Terminal014.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_5, 1137731567616000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_6, 42303703102696665907200000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_6⟩
theorem bound_56 : minorBindings polynomial_56 witness_56 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_56 witness_56 (by decide +kernel)
theorem positive_56 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_56 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_56 ρ hρ u
noncomputable def polynomial_57 : BiPoly := r7_rat_grid%[[660493610750958336,26360338943729074390,96597793136000610240],[0,26513814168774505200,65787636453775740000],[6200333834312902896,475637306671545929940,1280342169779725970640],[0,154882505919463354500,359226060560789175000],[23746934223546811200,2855249903739718031250,5188687661991616758000],[0,189897844693678509600,701137659710582910000],[47214898806038240160,6575726564328150961200,9059781299208688499400],[0,-8338490390389647600,556344247509737820000],[50841113951073862080,6402866946602361732000,6954997596353642707200],[0,-35678874156303470400,136903958847255600000],[27575843398796338128,2325060045579881423520,1832555111160060191520],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
noncomputable def witness_57 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_8, 4600, by norm_num, R7.Core.Certificates.Terminal014.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_9, 110400, by norm_num, R7.Core.Certificates.Terminal014.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_10, 1152, by norm_num, R7.Core.Certificates.Terminal014.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_11, 124416000, by norm_num, R7.Core.Certificates.Terminal014.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_12, 94058496000000, by norm_num, R7.Core.Certificates.Terminal014.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_13, 255989602713600000000, by norm_num, R7.Core.Certificates.Terminal014.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_14, 28554999594320249487360000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_14⟩
theorem bound_57 : minorBindings polynomial_57 witness_57 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_57 witness_57 (by decide +kernel)
theorem positive_57 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_57 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_57 ρ hρ u
noncomputable def polynomial_58 : BiPoly := r7_rat_grid%[[1422000625283752320,66759662962105159300,234052095785314408800],[0,42973459033570036000,110332237613690700000],[12882402591741799920,1082638937508555696300,2827548515785276567800],[0,226445535673861261200,557410184160011280000],[47542747213934542080,5929291759945994863500,10767547562520156037200],[0,253525593205554444000,997616525039379900000],[90797882319304308000,12821046717572831430000,17765657976709527345000],[0,-13854700111579267500,721257387273643500000],[93589870664260535040,11851337241724334256000,12894941928525490713600],[0,-42286073074137446400,162256543818969600000],[48400079121781183440,4080857602123980669600,3216431537286831309600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_58 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal014.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal014.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_18, 48000, by norm_num, R7.Core.Certificates.Terminal014.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_19, 2980800000000, by norm_num, R7.Core.Certificates.Terminal014.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_20, 42865200000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_21, 27776649600000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_22, 5164026257653401600000000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_22⟩
theorem bound_58 : minorBindings polynomial_58 witness_58 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_58 witness_58 (by decide +kernel)
theorem positive_58 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_58 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_58 ρ hρ u
noncomputable def polynomial_59 : BiPoly := r7_rat_grid%[[1994290934106637440,108288862485830566850,364988160523789269600],[0,36652519666067887000,118185982600784400000],[17250907694710387680,1573183081228947467700,4003923208276063816200],[0,178595326548810843600,539150258875947840000],[60499693657348333920,7799077874394745842750,14153525186650818427800],[0,181478587282922034000,861973447595109525000],[109386560306413299600,15634109257233168987000,21770295673709137689000],[0,-17321117618670106500,557250308142198300000],[106314809219488941120,13524730558672468968000,14736311901337166380800],[0,-29792460574960473600,114317110417910400000],[51653865953497565520,4355200970333996176800,3432662228869139296800],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_59 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal014.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_25, 920000, by norm_num, R7.Core.Certificates.Terminal014.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal014.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_27, 25920000000, by norm_num, R7.Core.Certificates.Terminal014.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_28, 2857680000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_29, 1851776640000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_30, 344268417176893440000000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_30⟩
theorem bound_59 : minorBindings polynomial_59 witness_59 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_59 witness_59 (by decide +kernel)
theorem positive_59 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_59 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_59 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry009
