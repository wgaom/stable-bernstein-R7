import R7.Spectral.SliceInteger
import R7.Spectral.CertificateCore
import R7.Algebra.CertificateDataLiteral
import R7.Certificates.Spectral.Terminal.Batches.Batch06
import R7.Certificates.Spectral.Terminal.Batches.Batch07
set_option Elab.async false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace R7.Core.SpectralSliceCertificates.Entry034
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_204 : BiPoly := r7_rat_grid%[[4087929562156540800,204491280822969245125,653856630454915422000],[0,7675296406594565000,137784715766815500000],[46349572035722646600,3865245998416096824000,10052432855465440756500],[0,154388484539036341500,947858095071333225000],[212510621917323500400,26344517339700158778750,47851315765661964411000],[0,301381749048455280000,2330621159216069250000],[501705500981713596000,70697553089706660195000,97888767634707378390000],[0,-121320771289454205000,2347798459979668500000],[635367323713823870400,80396934242686413660000,87456583756939563936000],[0,-200618585323322544000,769796670959316000000],[400622503655079543600,33778527210858159324000,26623403901071670924000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
noncomputable def witness_204 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_0, 57500, by norm_num, R7.Core.Certificates.Terminal051.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_1, 11500000, by norm_num, R7.Core.Certificates.Terminal051.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_2, 6000000, by norm_num, R7.Core.Certificates.Terminal051.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_3, 16200000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_4, 5103000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_5, 115736040000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_6, 215167760735558400000000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_6⟩
theorem bound_204 : minorBindings polynomial_204 witness_204 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_204 witness_204 (by decide +kernel)
theorem positive_204 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_204 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_204 ρ hρ u
noncomputable def polynomial_205 : BiPoly := r7_rat_grid%[[141056539504277760,5719953154326299900,16987408959795098400],[0,4274903465086129000,11343724195632300000],[1733575337588541600,118476605133332716500,325923872592807931500],[0,38252957800736666700,90657274214428605000],[8740473931622790000,994120429490374706250,1808835507703252350000],[0,70312948387481718000,261325655925315300000],[22868250512303674800,3116361891892541796000,4255294051480920282000],[0,-4819611637451016000,309634322362306200000],[32428069221388518720,4046129314932743388000,4382391377920142764800],[0,-30032722353790800000,115239022598700000000],[23183231175979222320,1954696498496360488800,1540643677523944408800],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
noncomputable def witness_205 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_8, 46000, by norm_num, R7.Core.Certificates.Terminal051.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_9, 9200000, by norm_num, R7.Core.Certificates.Terminal051.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_10, 6000000, by norm_num, R7.Core.Certificates.Terminal051.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_11, 2160000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_12, 2177280000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_13, 29628426240000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_14, 3672196449886863360000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_14⟩
theorem bound_205 : minorBindings polynomial_205 witness_205 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_205 witness_205 (by decide +kernel)
theorem positive_205 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_205 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_205 ρ hρ u
noncomputable def polynomial_206 : BiPoly := r7_rat_grid%[[939143070888837120,40485115968314927550,121619993225829040800],[0,21712447000623215000,47695599526270500000],[11440026011766318480,826141643185283769700,2233514077196371400700],[0,175469556709040608500,374749167720559275000],[56742138456452633520,6601400037233588007750,12006854082521042266800],[0,302227442478342864000,1056204976652755650000],[145963174148083900800,20069596489416422391000,27510125575098446622000],[0,-14965454187078192000,1210540656458624400000],[203188534994776161600,25451640212389849080000,27600359866048990944000],[0,-111000941819610796800,425923427524795200000],[142353173887591716000,12002522359188178440000,9460092756725974440000],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
noncomputable def witness_206 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_16, 69000, by norm_num, R7.Core.Certificates.Terminal051.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_17, 920000, by norm_num, R7.Core.Certificates.Terminal051.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal051.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_19, 8640000000, by norm_num, R7.Core.Certificates.Terminal051.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_20, 2351462400000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_21, 746636341248000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_22, 555236103222893740032000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_22⟩
theorem bound_206 : minorBindings polynomial_206 witness_206 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_206 witness_206 (by decide +kernel)
theorem positive_206 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_206 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_206 ρ hρ u
noncomputable def polynomial_207 : BiPoly := r7_rat_grid%[[2908547506812081600,135055904075425155875,417417805453269594000],[0,36695879243040655000,67582878887961000000],[34365119569749896400,2660811630779038883500,7053125294126364988500],[0,262639134667618456500,507364667861757975000],[165342611915836009200,19821821072293817006250,36030596491164111453000],[0,416109460244203080000,1363987758423168000000],[411551270947281483000,57248007763344321285000,78852181452216704595000],[0,-11710359260500792500,1462867331764592250000],[552684543239759112000,69565510048581495900000,75551265789966298080000],[0,-122533507203466464000,470175212202696000000],[372151868877561200400,31378022739020523636000,24731385349726476036000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
noncomputable def witness_207 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal051.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal051.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal051.polynomial_25, 34500000, by norm_num, R7.Core.Certificates.Terminal051.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal051.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal051.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal051.polynomial_27, 16200000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal051.polynomial_28, 6378750000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal051.polynomial_29, 434010150000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal051.polynomial_30, 806879102758344000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal051.positive_30⟩
theorem bound_207 : minorBindings polynomial_207 witness_207 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_207 witness_207 (by decide +kernel)
theorem positive_207 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_207 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_207 ρ hρ u
noncomputable def polynomial_208 : BiPoly := r7_rat_grid%[[5260040661856449600,262750807073309691500,835402678421566464000],[0,0,0],[59797874371350978000,4963342027503320820000,12918002478608754270000],[0,0,0],[275289288078629714400,34036792302323219797500,61828095784746979296000],[0,0,0],[653092518383653860000,91923911209742218200000,127223189600294394900000],[0,0,0],[832105429026226185600,105235011618964975440000,114456925248687895104000],[0,0,0],[528740360153912088000,44580797334127519920000,35137487382125047920000],[0,0,0],[125701082923343558400,-529522964639532864000,631277859625592256000]]
noncomputable def witness_208 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_0, 230000, by norm_num, R7.Core.Certificates.Terminal052.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_1, 405720000000, by norm_num, R7.Core.Certificates.Terminal052.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_2, 21168000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_3, 1143072000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_4, 760462940160000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_5, 4484297865535488000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_6, 11115826786522332675440640000000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_6⟩
theorem bound_208 : minorBindings polynomial_208 witness_208 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_208 witness_208 (by decide +kernel)
theorem positive_208 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_208 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_208 ρ hρ u
noncomputable def polynomial_209 : BiPoly := r7_rat_grid%[[257986726188001920,11662628252668013925,35328883173221872800],[0,4443868302682414000,6832213469686800000],[3119649999500346840,235355913892642810100,627871229708973803100],[0,30355341653415304200,51388672538636730000],[15260358330792131760,1809519374381231944500,3290173779705642608400],[0,45644298657948855000,136114004438404875000],[38679211305586438200,5360255406869398501500,7372121710327842888000],[0,-253309637362572000,140818844685852900000],[52952163665305302720,6656626133795809458000,7226592866144281324800],[0,-10451387379119198400,40103179864347600000],[36401740179827024520,3069216431849548486800,2419080862077070606800],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_209 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_8, 103500, by norm_num, R7.Core.Certificates.Terminal052.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal052.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal052.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_11, 4320000000, by norm_num, R7.Core.Certificates.Terminal052.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_12, 6531840000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_13, 14814213120000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_14, 2754147337415147520000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_14⟩
theorem bound_209 : minorBindings polynomial_209 witness_209 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_209 witness_209 (by decide +kernel)
theorem positive_209 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_209 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_209 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry034

namespace R7.Core.SpectralSliceCertificates.Entry035
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_210 : BiPoly := r7_rat_grid%[[1546234817410411200,73440873032020681750,227778616410784008000],[0,13855066706256320000,-9658086605091000000],[18150167167411150800,1433307251005196312000,3777821042095789384500],[0,59500084598241609000,-69604043093049150000],[86688529607656090800,10489071904075384447500,19063107747585345672000],[0,59416631600077350000,-186539617992268125000],[213950019491517618000,29879770231536704460000,41223807478133415495000],[0,31983718411473097500,-241501282595149500000],[284405308722846864000,35863764318459132300000,38971774896656333760000],[0,31234031247942432000,-119848583502648000000],[189126359593514708400,15946208277207151356000,12568408948221651756000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
noncomputable def witness_210 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_16, 115000, by norm_num, R7.Core.Certificates.Terminal052.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_17, 69000000, by norm_num, R7.Core.Certificates.Terminal052.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_18, 2000000, by norm_num, R7.Core.Certificates.Terminal052.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_19, 1800000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_20, 708750000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_21, 48223350000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_22, 44826616819908000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_22⟩
theorem bound_210 : minorBindings polynomial_210 witness_210 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_210 witness_210 (by decide +kernel)
theorem positive_210 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_210 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_210 ρ hρ u
noncomputable def polynomial_211 : BiPoly := r7_rat_grid%[[360507200776162560,17713720960140258775,55782563391091730400],[0,1098158379820114000,-10695448111723200000],[4140416867464113480,337966986509435714700,883257187129341950700],[0,-6555307814118660600,-79230289775856390000],[19415053512270304560,2386109387248921834500,4335069319328495660400],[0,-21877646017917915000,-210729851635312125000],[46900796491020609000,6591652685745283282500,9117401280925523310000],[0,13046797001951811000,-237419357723912700000],[60809959823833442880,7688879593587843462000,8362117092518252179200],[0,22944999878296171200,-88042613265406800000],[39248803657578858840,3309266879033312055600,2608282717211590095600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_211 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal052.polynomial_24, 11500, by norm_num, R7.Core.Certificates.Terminal052.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal052.polynomial_25, 460000, by norm_num, R7.Core.Certificates.Terminal052.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal052.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal052.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal052.polynomial_27, 21600000000, by norm_num, R7.Core.Certificates.Terminal052.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal052.polynomial_28, 2721600000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal052.polynomial_29, 6172588800000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal052.polynomial_30, 1147561390589644800000000000000000, by norm_num, R7.Core.Certificates.Terminal052.positive_30⟩
theorem bound_211 : minorBindings polynomial_211 witness_211 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_211 witness_211 (by decide +kernel)
theorem positive_211 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_211 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_211 ρ hρ u
noncomputable def polynomial_212 : BiPoly := r7_rat_grid%[[3271930040047680,110481330969579450,321837413376841200],[0,138365110058763000,472874749208100000],[40066016110430040,2287442104032131850,6708281991294603600],[0,1613502479987731800,4019768526956670000],[209262220537687380,22209607239058757250,40444350576155989200],[0,3392120759035068000,12530853004144050000],[566414010687531600,75127414155381927000,101311157346308694000],[0,-191991865738752000,16282085952978900000],[829340959162351680,102142501699127157000,110180366856817171200],[0,-1750478674335235200,6716788745752800000],[610085030946821640,51439381539377907600,40543254671682747600],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
noncomputable def witness_212 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal053.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_1, 4140000, by norm_num, R7.Core.Certificates.Terminal053.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_2, 54000, by norm_num, R7.Core.Certificates.Terminal053.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_3, 29160000000, by norm_num, R7.Core.Certificates.Terminal053.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_4, 217300320000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_5, 9183300480000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_6, 30487327031335680000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_6⟩
theorem bound_212 : minorBindings polynomial_212 witness_212 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_212 witness_212 (by decide +kernel)
theorem positive_212 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_212 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_212 ρ hρ u
noncomputable def polynomial_213 : BiPoly := r7_rat_grid%[[24093303022169280,843324393744602825,2341163642334535200],[0,922125671017299000,3047668796323800000],[303637553464337460,17833266895378631900,51515510343060033900],[0,10534312107332378100,26073677985654015000],[1594669768185004560,170685405292451683875,310838761613668347900],[0,22221968803553376000,81739219934660850000],[4351089445736038200,579316363575519879000,782767792185562638000],[0,-1292074197002649000,106958772939084300000],[6433675319562485760,794144206708919874000,857241178505728358400],[0,-11652696273270830400,44712740768295600000],[4793525243153598600,404166569237969274000,318554143848935874000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_213 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal053.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal053.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal053.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_11, 2880000000, by norm_num, R7.Core.Certificates.Terminal053.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_12, 77760000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_13, 377913600000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_14, 10036980092620800000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_14⟩
theorem bound_213 : minorBindings polynomial_213 witness_213 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_213 witness_213 (by decide +kernel)
theorem positive_213 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_213 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_213 ρ hρ u
noncomputable def polynomial_214 : BiPoly := r7_rat_grid%[[88961794800993360,3398621295902240775,9513254770371752400],[0,2838361855921701000,8899161627638700000],[1113337696035904020,70207799715578340300,197622418510363749300],[0,30593526280867001400,75316967782051410000],[5782969101866309640,635500896436934858625,1156933613668275867600],[0,62809085482378434000,232654749963549525000],[15610713415766969400,2099320943622549295500,2849710006485836271000],[0,-4007931999094611000,299943830186147700000],[22855045170047333040,2834164616044118931000,3063794171143272033600],[0,-32195078363263737600,123536232225806400000],[16879019189528732040,1423156222589455443600,1121696712583222683600],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_214 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_16, 34500, by norm_num, R7.Core.Certificates.Terminal053.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_17, 4140000, by norm_num, R7.Core.Certificates.Terminal053.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_18, 432000, by norm_num, R7.Core.Certificates.Terminal053.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_19, 38880000000, by norm_num, R7.Core.Certificates.Terminal053.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_20, 4898880000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_21, 11110659840000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_22, 1032805251530680320000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_22⟩
theorem bound_214 : minorBindings polynomial_214 witness_214 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_214 witness_214 (by decide +kernel)
theorem positive_214 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_214 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_214 ρ hρ u
noncomputable def polynomial_215 : BiPoly := r7_rat_grid%[[205883719035121440,8578932701569361225,24916635405640329600],[0,4701478447306283000,15253511059119600000],[2535288463876656420,174394216269236571300,477755968424364465300],[0,48587262179558612700,125331231465076005000],[12873445216727220720,1466392176125020259625,2668005033540888552300],[0,95977221966833112000,373694272353058950000],[33924766427997157800,4626617388089034636000,6319262493648355752000],[0,-8065405326698118000,464514055321692600000],[48407542752723729120,6040854609904984338000,6543205407334726300800],[0,-47932224876650116800,183921480067525200000],[34774846763968833480,2932044747744540733200,2310965516285916613200],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_215 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal053.polynomial_24, 11500, by norm_num, R7.Core.Certificates.Terminal053.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal053.polynomial_25, 460000, by norm_num, R7.Core.Certificates.Terminal053.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal053.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal053.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal053.polynomial_27, 8640000000, by norm_num, R7.Core.Certificates.Terminal053.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal053.polynomial_28, 2177280000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal053.polynomial_29, 844410147840000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal053.polynomial_30, 156986398232663408640000000000000000, by norm_num, R7.Core.Certificates.Terminal053.positive_30⟩
theorem bound_215 : minorBindings polynomial_215 witness_215 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_215 witness_215 (by decide +kernel)
theorem positive_215 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_215 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_215 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry035

namespace R7.Core.SpectralSliceCertificates.Entry036
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_216 : BiPoly := r7_rat_grid%[[326325446797179600,14787489661014394625,44905751562333414000],[0,3520805179197955000,16347306307783500000],[3898580489176648500,293164429547062740000,783114287032208677500],[0,39789166842280050000,128096573205532500000],[19139092141147612200,2266865009662416376875,4121445489253873848000],[0,78070282590402450000,362363099735098125000],[48617202584013129000,6734005543710694642500,9258399704836640610000],[0,-11991212940451500000,427223859975675000000],[66630006605429845200,8372300127854095755000,9087907111679701368000],[0,-42045811295307120000,161334631638180000000],[45756377321011623000,3857953615453343070000,3040744100376206070000],[0,0,0],[11784476524063458600,-49642777934956206000,59182299339899274000]]
noncomputable def witness_216 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_0, 57500, by norm_num, R7.Core.Certificates.Terminal054.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_1, 57500000, by norm_num, R7.Core.Certificates.Terminal054.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_2, 750000000, by norm_num, R7.Core.Certificates.Terminal054.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_3, 1012500000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_4, 11481750000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_5, 5859137025000000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_6, 1361608485904705500000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_6⟩
theorem bound_216 : minorBindings polynomial_216 witness_216 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_216 witness_216 (by decide +kernel)
theorem positive_216 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_216 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_216 ρ hρ u
noncomputable def polynomial_217 : BiPoly := r7_rat_grid%[[22011165723957120,802798139732570050,2107627977654340800],[0,737330461564494000,2312339598982800000],[286746978045234600,17366996958500209000,49364764755763239000],[0,8160604374762901800,19989207755654670000],[1515241772068510080,163693952672433309750,298122718618088782200],[0,17306971534826208000,63231615836169300000],[4170866805971823600,557613413907984342000,755046325600655724000],[0,-1048213468095282000,83660858254337400000],[6232622965826158080,771148399824822492000,833039422156919347200],[0,-9301563151859779200,35691171570568800000],[4706370238732624080,396818086160915287200,312762250324409767200],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
noncomputable def witness_217 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal054.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_9, 9200000, by norm_num, R7.Core.Certificates.Terminal054.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_10, 16000000, by norm_num, R7.Core.Certificates.Terminal054.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_11, 5760000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_12, 311040000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_13, 16325867520000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_14, 433597540001218560000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_14⟩
theorem bound_217 : minorBindings polynomial_217 witness_217 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_217 witness_217 (by decide +kernel)
theorem positive_217 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_217 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_217 ρ hρ u
noncomputable def polynomial_218 : BiPoly := r7_rat_grid%[[158936480430194880,6228960811260483700,16424620532127589200],[0,4127610777515642000,12578852564802900000],[2039176911450449160,128611471805581339900,360117047595847649400],[0,44096285112651660900,107761355341913835000],[10726852706296831440,1176843818809993371750,2142892713175875017100],[0,91723692103276194000,337010777351464275000],[29384872312031942400,3951547167188618230500,5365255537508537466000],[0,-5884755057199746000,440790698515192200000],[43745641300462631040,5427749383065570456000,5868542778296203353600],[0,-48412748434310769600,185765304429104400000],[32944591671128368560,2777726603126407010400,2189335752270868370400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_218 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal054.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal054.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal054.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_19, 1440000000, by norm_num, R7.Core.Certificates.Terminal054.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_20, 725760000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_21, 266655836160000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_22, 49574652073472655360000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_22⟩
theorem bound_218 : minorBindings polynomial_218 witness_218 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_218 witness_218 (by decide +kernel)
theorem positive_218 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_218 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_218 ρ hρ u
noncomputable def polynomial_219 : BiPoly := r7_rat_grid%[[542148892696385280,22741065102541354700,62736962459839975200],[0,8986091053350336000,28399802994425700000],[6833481636612234600,462476773148632274000,1267956610484237176500],[0,93135031517014908300,236663428537407645000],[35231407815877897680,3978499321786834686000,7240650606517833353700],[0,187337742881596308000,717075449611460550000],[94505319480168151200,12848701313157848131500,17529269388516271683000],[0,-14913342577204879500,908041385476105650000],[137628713313921977280,17157806722206362772000,18578862180884561875200],[0,-96224842421545723200,369225828406234800000],[101274115137172392240,8538937335536732661600,6730180275499336101600],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_219 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal054.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal054.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal054.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_27, 540000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_28, 17010000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_29, 231472080000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_30, 129100656441335040000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_30⟩
theorem bound_219 : minorBindings polynomial_219 witness_219 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_219 witness_219 (by decide +kernel)
theorem positive_219 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_219 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_219 ρ hρ u
noncomputable def polynomial_220 : BiPoly := r7_rat_grid%[[1131294598695273600,50547818191460795250,148301058623944374000],[0,5260360958017480000,31141112766651000000],[13814919476508083400,1011590581964052788500,2716209304833911818500],[0,69304633357119009000,245867208815885850000],[68990342780673090000,8065329464498722755000,14668502307436341225000],[0,145703793783853890000,706130256889128375000],[178763694585170958000,24633926591414019210000,33799426519234891095000],[0,-24981993350442922500,852418951348245750000],[250687153564983576000,31433835265152371100000,34098503154335655840000],[0,-87695549273069136000,336497945988204000000],[176924658974578275600,14917420646419593204000,11757543854787996804000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
noncomputable def witness_220 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_0, 345000, by norm_num, R7.Core.Certificates.Terminal055.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_1, 23000000, by norm_num, R7.Core.Certificates.Terminal055.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_2, 2000000, by norm_num, R7.Core.Certificates.Terminal055.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_3, 1800000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_4, 6378750000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_5, 434010150000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_6, 403439551379172000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_6⟩
theorem bound_220 : minorBindings polynomial_220 witness_220 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_220 witness_220 (by decide +kernel)
theorem positive_220 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_220 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_220 ρ hρ u
noncomputable def polynomial_221 : BiPoly := r7_rat_grid%[[81897400396344960,3419167322196488525,9047922610337396400],[0,1546954162039913000,4485663968363100000],[1035562488292128060,67826982450830608400,187340370950676312900],[0,15534169800981504600,37799128197122490000],[5423506504057046160,603914984456476787625,1099463198012564279400],[0,31149291731384466000,115700121924871725000],[14786838491130559800,1999900218510673033500,2722593397906242432000],[0,-2216007918866259000,147977694625011300000],[21931460920071077760,2728729983678691734000,2952904800746985638400],[0,-15857277402801542400,60846203932113600000],[16472295835564184280,1388863301563203505200,1094667876135434185200],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
noncomputable def witness_221 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal055.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal055.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal055.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_11, 4320000000, by norm_num, R7.Core.Certificates.Terminal055.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_12, 544320000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_13, 99995938560000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_14, 9295247263776122880000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_14⟩
theorem bound_221 : minorBindings polynomial_221 witness_221 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_221 witness_221 (by decide +kernel)
theorem positive_221 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_221 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_221 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry036

namespace R7.Core.SpectralSliceCertificates.Entry037
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_222 : BiPoly := r7_rat_grid%[[532878424249583520,22841205288248669175,62237501130578716800],[0,5709612126346797000,14389091814438900000],[6717342563769256020,458637981074448210300,1252009551313725616800],[0,52766729599409168400,119592947148474960000],[34697814611197857840,3930704620473764363625,7153756391394848955600],[0,99709938032324004000,358257931323255900000],[93278089123678499400,12699249957927597055500,17337356459455693221000],[0,-6048283274874823500,445150345036896450000],[136250666972687564640,16999730956702582956000,18412327760826708777600],[0,-45409476198931689600,174241402169234400000],[100664030106225570600,8487497953997354754000,6689637020827653354000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
noncomputable def witness_222 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_16, 103500, by norm_num, R7.Core.Certificates.Terminal055.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_17, 4140000, by norm_num, R7.Core.Certificates.Terminal055.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_18, 432000, by norm_num, R7.Core.Certificates.Terminal055.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_19, 116640000000, by norm_num, R7.Core.Certificates.Terminal055.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_20, 11022480000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_21, 1124954308800000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_22, 627429190304888294400000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_22⟩
theorem bound_222 : minorBindings polynomial_222 witness_222 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_222 witness_222 (by decide +kernel)
theorem positive_222 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_222 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_222 ρ hρ u
noncomputable def polynomial_223 : BiPoly := r7_rat_grid%[[1627041574460073600,72610142039403464000,210399901667600124000],[0,0,0],[19932188341473088200,1447119254712532198000,3891397635552769938000],[0,0,0],[100053817415720065800,11645029806762254786250,21181286046791030922000],[0,0,0],[260807905830213414000,35873421118743949155000,49184699250425823135000],[0,0,0],[368407495268306272800,46158494477714214120000,50059169159743768752000],[0,0,0],[262336563307133305200,22118934061932500268000,17433599508823581468000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
noncomputable def witness_223 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_24, 1840000, by norm_num, R7.Core.Certificates.Terminal055.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_25, 36064000000, by norm_num, R7.Core.Certificates.Terminal055.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_26, 784000000, by norm_num, R7.Core.Certificates.Terminal055.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_27, 2116800000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_28, 10668672000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_29, 31213547043840000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_30, 43522413299502868684800000000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_30⟩
theorem bound_223 : minorBindings polynomial_223 witness_223 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_223 witness_223 (by decide +kernel)
theorem positive_223 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_223 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_223 ρ hρ u
noncomputable def polynomial_224 : BiPoly := r7_rat_grid%[[191457482040365760,8389135547772802400,23395822199711018400],[0,712499760151372000,621399939566400000],[2407103399261914560,170104689147970923400,459992292307797785400],[0,4109480130976436400,4130375038071660000],[12284863399351146240,1412639778069556000500,2570244531571437411600],[0,4174708558780404000,7438377032427150000],[32611715766857880000,4466366201597051970000,6113050843824643950000],[0,399826987815969000,811507441241700000],[46970856141649554240,5875694003777671836000,6369075572390501241600],[0,1441570672981958400,-5531473084737600000],[34164761733022011840,2880605366205162825600,2270422261614233865600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
noncomputable def witness_224 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal056.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_1, 88320000, by norm_num, R7.Core.Certificates.Terminal056.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal056.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_3, 1152000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_4, 979776000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_5, 53331167232000000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_6, 9914930414694531072000000000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_6⟩
theorem bound_224 : minorBindings polynomial_224 witness_224 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_224 witness_224 (by decide +kernel)
theorem positive_224 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_224 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_224 ρ hρ u
noncomputable def polynomial_225 : BiPoly := r7_rat_grid%[[3985805685148992,152454377144107455,374818462594829280],[0,110507050422337800,315402080328360000],[53971280525226348,3380145404324357220,9442803833693288820],[0,1157379328438685100,2780947505131065000],[287162755190403120,31340500010482987125,57081335124501843300],[0,2478394853219808000,8944802347535550000],[798128833241521800,107182092848089761000,145464971803149762000],[0,-160870547837583000,12072588713918100000],[1206314122417966080,149630518588145022000,161767533161622067200],[0,-1390086006089745600,5333920474568400000],[923843046862329912,77893920616772260080,61394071359976732080],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
noncomputable def witness_225 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_8, 6900, by norm_num, R7.Core.Certificates.Terminal056.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_9, 165600, by norm_num, R7.Core.Certificates.Terminal056.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_10, 3456, by norm_num, R7.Core.Certificates.Terminal056.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_11, 42923520000, by norm_num, R7.Core.Certificates.Terminal056.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_12, 151165440000000, by norm_num, R7.Core.Certificates.Terminal056.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_13, 29386561536000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_14, 156095114400438681600000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_14⟩
theorem bound_225 : minorBindings polynomial_225 witness_225 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_225 witness_225 (by decide +kernel)
theorem positive_225 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_225 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_225 ρ hρ u
noncomputable def polynomial_226 : BiPoly := r7_rat_grid%[[27989874251680608,1132135806143297170,2764546304702334720],[0,515699568637576400,1471876374865680000],[370335686165818056,23361468836001199840,64997851634193560040],[0,5401103532713863800,12977755023944970000],[1977553441772208720,216537168949223405250,394383639803039659800],[0,11565842648359104000,41742410955165900000],[5509663558505989200,740890489426427574000,1006218212409080478000],[0,-750729223242054000,56338747331617800000],[8356238452166119200,1037433906808580610000,1121899442861172528000],[0,-6487068028418812800,24891628881319200000],[6426228992639854608,541828152214780626720,427055615875058274720],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_226 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_16, 4600, by norm_num, R7.Core.Certificates.Terminal056.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_17, 3606400, by norm_num, R7.Core.Certificates.Terminal056.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_18, 50176, by norm_num, R7.Core.Certificates.Terminal056.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_19, 18063360000, by norm_num, R7.Core.Certificates.Terminal056.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_20, 34139750400000000, by norm_num, R7.Core.Certificates.Terminal056.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_21, 30971581562880000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_22, 1151600806684520349696000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_22⟩
theorem bound_226 : minorBindings polynomial_226 witness_226 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_226 witness_226 (by decide +kernel)
theorem positive_226 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_226 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_226 ρ hρ u
noncomputable def polynomial_227 : BiPoly := r7_rat_grid%[[93329325657481248,3949066420074925145,10144803740551792320],[0,773549352956364600,2207814562298520000],[1212219576318899988,80354179497910966820,220529063139076191420],[0,8101655299070795700,19466632535917455000],[6368495996314826640,711564423039721718625,1295457222482600210100],[0,17348763972538656000,62613616432748850000],[17447267935268965800,2363510092409718471000,3220150259217495222000],[0,-1126093834863081000,84508120997426700000],[26006959673934553440,3238609922939554506000,3505621627952988969600],[0,-9730602042628219200,37337443321978800000],[19644737996487656808,1656348085567968624720,1305492800428184472720],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
noncomputable def witness_227 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_24, 2300, by norm_num, R7.Core.Certificates.Terminal056.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_25, 901600, by norm_num, R7.Core.Certificates.Terminal056.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_26, 6272, by norm_num, R7.Core.Certificates.Terminal056.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_27, 3386880000, by norm_num, R7.Core.Certificates.Terminal056.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_28, 213373440000000, by norm_num, R7.Core.Certificates.Terminal056.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_29, 290358577152000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_30, 32388772688002134835200000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_30⟩
theorem bound_227 : minorBindings polynomial_227 witness_227 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_227 witness_227 (by decide +kernel)
theorem positive_227 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_227 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_227 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry037

namespace R7.Core.SpectralSliceCertificates.Entry038
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
noncomputable def polynomial_228 : BiPoly := r7_rat_grid%[[28079108707318272,1197090972277842155,2905363371240864480],[0,257849784318788200,735938187432840000],[362872408655051676,23061919841731899140,63896076432534098340],[0,2700551766356931900,6488877511972485000],[1944967597211595600,213690837825065900625,389197933734566416500],[0,5782921324179552000,20871205477582950000],[5432425284321325800,731506328916226821000,994181622196112622000],[0,-375364611621027000,28169373665808900000],[8268278047406475840,1027454183500146066000,1111426153590990585600],[0,-3243534014209406400,12445814440659600000],[6385556657243399832,538398860112155432880,424352732230279424880],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
noncomputable def witness_228 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_0, 2300, by norm_num, R7.Core.Certificates.Terminal057.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_1, 901600, by norm_num, R7.Core.Certificates.Terminal057.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_2, 6272, by norm_num, R7.Core.Certificates.Terminal057.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_3, 1128960000, by norm_num, R7.Core.Certificates.Terminal057.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_4, 213373440000000, by norm_num, R7.Core.Certificates.Terminal057.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_5, 96786192384000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_6, 3598752520889126092800000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_6⟩
theorem bound_228 : minorBindings polynomial_228 witness_228 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_228 witness_228 (by decide +kernel)
theorem positive_228 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_228 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_228 ρ hρ u
noncomputable def polynomial_229 : BiPoly := r7_rat_grid%[[177566651779436064,7540339336908451610,18860893854274385760],[0,0,0],[2300836802284055016,149539939023106664240,412217292436678486440],[0,0,0],[12203398787949613440,1352636936514919420500,2463051023686299459600],[0,0,0],[33744543788232943200,4558029079158398934000,6202695125805833088000],[0,0,0],[50811793816153980960,6320972473439992704000,6839900088725960726400],[0,0,0],[38801407968217856304,3271544665904434923360,2578550997119022747360],[0,0,0],[11313097463100920256,-47657066817557957760,56815007366303303040]]
noncomputable def witness_229 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_8, 4600, by norm_num, R7.Core.Certificates.Terminal057.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_9, 3606400, by norm_num, R7.Core.Certificates.Terminal057.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_10, 50176, by norm_num, R7.Core.Certificates.Terminal057.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_11, 54190080000, by norm_num, R7.Core.Certificates.Terminal057.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_12, 54623600640000000, by norm_num, R7.Core.Certificates.Terminal057.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_13, 23637511048790016000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_14, 5273410413969755585327923200000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_14⟩
theorem bound_229 : minorBindings polynomial_229 witness_229 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_229 witness_229 (by decide +kernel)
theorem positive_229 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_229 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_229 ρ hρ u
noncomputable def polynomial_230 : BiPoly := r7_rat_grid%[[4694723860492656,210341023068731190,507696739629899040],[0,0,0],[59234855190714216,3793728474577099740,10465716871812439440],[0,0,0],[318730292108497080,35140751116818066000,64002037944348862200],[0,0,0],[892531168356110400,120353694734337678000,163690838663857461000],[0,0,0],[1363386273774472080,169579076698618587000,183492144053468107200],[0,0,0],[1057480720307824176,89161594668255039840,70274974764250095840],[0,0,0],[314252707308358896,-1323807411598832160,1578194649063980640]]
noncomputable def witness_230 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal057.polynomial_16, 13800, by norm_num, R7.Core.Certificates.Terminal057.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal057.polynomial_17, 16228800, by norm_num, R7.Core.Certificates.Terminal057.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal057.polynomial_18, 169344, by norm_num, R7.Core.Certificates.Terminal057.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal057.polynomial_19, 91445760000, by norm_num, R7.Core.Certificates.Terminal057.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal057.polynomial_20, 69132994560000000, by norm_num, R7.Core.Certificates.Terminal057.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal057.polynomial_21, 815326884642816000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal057.polynomial_22, 5052648539328333034291200000000000, by norm_num, R7.Core.Certificates.Terminal057.positive_22⟩
theorem bound_230 : minorBindings polynomial_230 witness_230 := by
  exact R7.Core.SpectralCertificate.IntegerSlices.band_accepted polynomial_230 witness_230 (by decide +kernel)
theorem positive_230 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_230 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_230 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry038
