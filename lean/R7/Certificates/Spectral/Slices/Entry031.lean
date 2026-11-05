import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal046
import R7.Certificates.Spectral.Terminal.Terminal047

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry031
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_186 : BiPoly := [[244502408447199360,13925177556453886400,45475082130012542400],[0,686602427524248000,-17406843196172400000],[2542228002614737440,237165016354505721600,598918367667596394600],[0,-8466526722047869200,-107368996164103980000],[10536089741264908800,1374483959327332695000,2493682991663515542000],[0,-18044011994042862000,-234177753906396450000],[22210294843323208800,3192053949663925221000,4454459243107645842000],[0,13652865943289397000,-202231359115542900000],[24737816690973984960,3155115287770623684000,3440445714316350086400],[0,14415706729819584000,-55314730847376000000],[13479974017110725760,1136565382584349958400,895812865126704518400],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_186 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_16, 736000, by norm_num, R7.Core.Certificates.Terminal046.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_17, 176640000, by norm_num, R7.Core.Certificates.Terminal046.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_18, 3456000, by norm_num, R7.Core.Certificates.Terminal046.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_19, 622080000000, by norm_num, R7.Core.Certificates.Terminal046.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_20, 128770560000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_21, 29023764480000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_22, 1541680142226554880000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_22⟩
theorem bound_186 : minorBindings polynomial_186 witness_186 := by
 decide +kernel
theorem positive_186 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_186 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_186 ρ hρ u
def polynomial_187 : BiPoly := [[1850788709521920,33119501361543300,133322006904172800],[0,102191307402573000,416583000192600000],[24091983543526560,1177706157508260900,3753201545309052900],[0,1265214174391194300,3435718776426045000],[120839173578940320,12265772961740470875,22323950755853316300],[0,2689306098977331000,10127256302285100000],[311813773560307800,40572351854457223500,54175549845463002000],[0,-121060378256953500,12223204031693700000],[431424842392536480,52679216839017177000,56668980714916003200],[0,-1181287079249104800,4532734888882200000],[295358626093302540,24903192650016288600,19628083610894028600],[0,0,0],[74822073168656880,-315192240856864800,375760630729519200]]
def witness_187 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_24, 138000, by norm_num, R7.Core.Certificates.Terminal046.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_25, 49680000, by norm_num, R7.Core.Certificates.Terminal046.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_26, 3888000, by norm_num, R7.Core.Certificates.Terminal046.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_27, 349920000000, by norm_num, R7.Core.Certificates.Terminal046.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_28, 1574640000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_29, 85030560000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_30, 125462251157760000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_30⟩
theorem bound_187 : minorBindings polynomial_187 witness_187 := by
 decide +kernel
theorem positive_187 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_187 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_187 ρ hρ u
def polynomial_188 : BiPoly := [[15467305643861760,346025449462032400,1229048592594158400],[0,797634657827122000,3129997666766400000],[197973256075066080,10116159750425741200,31463585260247122200],[0,9742621686330808200,25974004027831830000],[1004051335523891760,103207447422521168250,187869505303327883400],[0,20658664272577410000,77471341819236000000],[2626101322278555600,343603996667252577000,460134842201189604000],[0,-982351423860057000,95048672127467400000],[3694336999905021120,452265303299605938000,486921040098585580800],[0,-9421694041274942400,36152127660963600000],[2585598464488910760,218004997952601608400,171826174560941168400],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_188 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_0, 184000, by norm_num, R7.Core.Certificates.Terminal047.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_1, 14720000, by norm_num, R7.Core.Certificates.Terminal047.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal047.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_3, 23040000000, by norm_num, R7.Core.Certificates.Terminal047.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_4, 1866240000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_5, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_6, 8029584074096640000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_6⟩
theorem bound_188 : minorBindings polynomial_188 witness_188 := by
 decide +kernel
theorem positive_188 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_188 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_188 ρ hρ u
def polynomial_189 : BiPoly := [[63257314107588480,1725174097523561450,5852576441775763200],[0,3099348465907361000,11178440905880700000],[798439758958831320,44914208815951912300,134100847992259581300],[0,34897923797299601100,91455795185758965000],[4022315187950682000,426597632034241897500,776430681282865755000],[0,71630899256549124000,270087198300601650000],[10470077167254372000,1386457319316945195000,1867508646409531980000],[0,-3876163869472803000,328248875277872100000],[14685199004157600960,1807363440495754884000,1949151790152379526400],[0,-32435340142094064000,124458144406596000000],[10284290521674993360,867121003092370442400,683443435894080602400],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_189 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal047.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_9, 2760000, by norm_num, R7.Core.Certificates.Terminal047.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal047.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_11, 43200000000, by norm_num, R7.Core.Certificates.Terminal047.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_12, 388800000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_13, 755827200000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_14, 40147920370483200000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_14⟩
theorem bound_189 : minorBindings polynomial_189 witness_189 := by
 decide +kernel
theorem positive_189 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_189 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_189 ρ hρ u
def polynomial_190 : BiPoly := [[164819344542603840,5362171085153516600,18058305641488245600],[0,7280154003893884000,24841673491375800000],[2034201393109938240,128161001674649268600,366785662785663216600],[0,74648253752314932000,197169294195145800000],[10071741456276171840,1114145977616534883000,2026959189866875965600],[0,145330412774032818000,564865123555894050000],[25757534102174416800,3467616471984586671000,4706611221712379562000],[0,-10087152913615869000,663711165517938300000],[35477363253056155200,4399000124311695420000,4755276958586460768000],[0,-63429109611206169600,243384815728454400000],[24403401237872865600,2057575261575116304000,1621730186867309904000],[0,0,0],[6285054146167177920,-26476148231976643200,31563892981279612800]]
def witness_190 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_16, 92000, by norm_num, R7.Core.Certificates.Terminal047.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_17, 7360000, by norm_num, R7.Core.Certificates.Terminal047.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_18, 384000, by norm_num, R7.Core.Certificates.Terminal047.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_19, 69120000000, by norm_num, R7.Core.Certificates.Terminal047.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_20, 21772800000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_21, 5925685248000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_22, 734439289977372672000000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_22⟩
theorem bound_190 : minorBindings polynomial_190 witness_190 := by
 decide +kernel
theorem positive_190 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_190 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_190 ρ hρ u
def polynomial_191 : BiPoly := [[298637978200715520,11438675800749541050,38495228763653596800],[0,10690662685386342000,37760116013667900000],[3584599094951775180,253436259801903377700,697387342105364753700],[0,101617613529557645400,286510510825325010000],[17268461001839915280,2001233869344677115375,3638527145552584937700],[0,185797080851786037000,781724893732804575000],[42892988263883074800,5883257591689170568500,8051748330545236782000],[0,-18857342829074715000,868368490008925500000],[57232903363607946240,7156983521015218926000,7757142493305658521600],[0,-78205209009271243200,300082414847014800000],[38028633595685215560,3206388115954556240400,2527196207868224600400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_191 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal047.polynomial_24, 69000, by norm_num, R7.Core.Certificates.Terminal047.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal047.polynomial_25, 1713960000, by norm_num, R7.Core.Certificates.Terminal047.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal047.polynomial_26, 268272000, by norm_num, R7.Core.Certificates.Terminal047.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal047.polynomial_27, 24144480000000, by norm_num, R7.Core.Certificates.Terminal047.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal047.polynomial_28, 3042204480000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal047.polynomial_29, 6899719760640000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal047.polynomial_30, 1282744122401104957440000000000000000, by norm_num, R7.Core.Certificates.Terminal047.positive_30⟩
theorem bound_191 : minorBindings polynomial_191 witness_191 := by
 decide +kernel
theorem positive_191 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_191 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_191 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry031
