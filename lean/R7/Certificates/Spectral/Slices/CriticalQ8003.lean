import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal111
import R7.Certificates.Spectral.Terminal.Terminal112

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.CriticalQ8003
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_18 : BiPoly := [[109595502126],[265151279250],[1741231368252],[989117113500],[5159926616976],[999704160000],[4470947934984],[0],[77789294352]]
def witness_18 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_3, 219191004252, by norm_num, R7.Core.Certificates.Terminal111.positive_3⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_4, 693019303596568339052508, by norm_num, R7.Core.Certificates.Terminal111.positive_4⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_5, 6937411398429520160800770506009351616, by norm_num, R7.Core.Certificates.Terminal111.positive_5⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_6, 61341001013296883068924306909791679625851126668288, by norm_num, R7.Core.Certificates.Terminal111.positive_6⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_7, 9543346367339363006025356028426744954831629041860584591818752, by norm_num, R7.Core.Certificates.Terminal111.positive_7⟩
theorem bound_18 : ordinaryBindings polynomial_18 witness_18 := by
 decide +kernel
theorem positive_18 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_18 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_18 ρ hρ u
def polynomial_19 : BiPoly := [[417229603155],[631192023750],[5292893911875],[2181570817500],[14436645111936],[1963704600000],[11554135112880],[0],[194473235880]]
def witness_19 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_8, 834459206310, by norm_num, R7.Core.Certificates.Terminal111.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_9, 8435004734726866603800000, by norm_num, R7.Core.Certificates.Terminal111.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_10, 239574938740012573585413180813476100000, by norm_num, R7.Core.Certificates.Terminal111.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_11, 5503635900363983073657503095805216649797364336000000, by norm_num, R7.Core.Certificates.Terminal111.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_12, 2140619765298242116279446027764716272141092377434455151360000000, by norm_num, R7.Core.Certificates.Terminal111.positive_12⟩
theorem bound_19 : ordinaryBindings polynomial_19 witness_19 := by
 decide +kernel
theorem positive_19 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_19 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_19 ρ hρ u
def polynomial_20 : BiPoly := [[906431149930],[895439970000],[9455864426670],[2705086417500],[23127286748832],[2023210800000],[16577672118480],[0],[259297647840]]
def witness_20 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_13, 1812862299860, by norm_num, R7.Core.Certificates.Terminal111.positive_13⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_14, 33482547523521072142532400, by norm_num, R7.Core.Certificates.Terminal111.positive_14⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_15, 1535455348985581247495989885834319313600, by norm_num, R7.Core.Certificates.Terminal111.positive_15⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_16, 50771493800719118056814849361328149928416182950656000, by norm_num, R7.Core.Certificates.Terminal111.positive_16⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_17, 26329857839699218025302723843552631069634361231392423169966080000, by norm_num, R7.Core.Certificates.Terminal111.positive_17⟩
theorem bound_20 : ordinaryBindings polynomial_20 witness_20 := by
 decide +kernel
theorem positive_20 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_20 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_20 ρ hρ u
def polynomial_21 : BiPoly := [[1181122944645],[805897796250],[10222364906955],[2052801112500],[21963310406784],[1249630200000],[13814726765400],[0],[194473235880]]
def witness_21 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_18, 2362245889290, by norm_num, R7.Core.Certificates.Terminal111.positive_18⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_19, 47646007702552997647961400, by norm_num, R7.Core.Certificates.Terminal111.positive_19⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_20, 2082973627388313927797253266348097775200, by norm_num, R7.Core.Certificates.Terminal111.positive_20⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_21, 57477020198990527035278185742783659605607264676160000, by norm_num, R7.Core.Certificates.Terminal111.positive_21⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_22, 22355484213675618604034343394749639284581778708016910985241600000, by norm_num, R7.Core.Certificates.Terminal111.positive_22⟩
theorem bound_21 : ordinaryBindings polynomial_21 witness_21 := by
 decide +kernel
theorem positive_21 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_21 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_21 ρ hρ u
def polynomial_22 : BiPoly := [[873488843616],[444588506250],[6267054827436],[982787967000],[11558736949968],[499852080000],[6279421257000],[0],[77789294352]]
def witness_22 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_23, 1746977687232, by norm_num, R7.Core.Certificates.Terminal111.positive_23⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_24, 21699150956490961991931804, by norm_num, R7.Core.Certificates.Terminal111.positive_24⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_25, 499942198726157406127928304442783964544, by norm_num, R7.Core.Certificates.Terminal111.positive_25⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_26, 6273273761429204514049610561098955976371830223616000, by norm_num, R7.Core.Certificates.Terminal111.positive_26⟩
 | 4 => ⟨R7.Core.Certificates.Terminal111.polynomial_27, 975987078356989228305224550936589134091755716531670011633664000, by norm_num, R7.Core.Certificates.Terminal111.positive_27⟩
theorem bound_22 : ordinaryBindings polynomial_22 witness_22 := by
 decide +kernel
theorem positive_22 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_22 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_22 ρ hρ u
def polynomial_23 : BiPoly := [[291162947872],[134414173500],[1690067613804],[248002302000],[2601489960384],[107111160000],[1205648881344],[0],[12964882392]]
def witness_23 : Fin 5 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal111.polynomial_28, 582325895744, by norm_num, R7.Core.Certificates.Terminal111.positive_28⟩
 | 1 => ⟨R7.Core.Certificates.Terminal111.polynomial_29, 1950273104114989816250352, by norm_num, R7.Core.Certificates.Terminal111.positive_29⟩
 | 2 => ⟨R7.Core.Certificates.Terminal111.polynomial_30, 10111415763934197135866105140036110336, by norm_num, R7.Core.Certificates.Terminal111.positive_30⟩
 | 3 => ⟨R7.Core.Certificates.Terminal111.polynomial_31, 24359259114750386620345460777947093804675511943168, by norm_num, R7.Core.Certificates.Terminal111.positive_31⟩
 | 4 => ⟨R7.Core.Certificates.Terminal112.polynomial_0, 631629859157985589938618506794265796751619664131129015795712, by norm_num, R7.Core.Certificates.Terminal112.positive_0⟩
theorem bound_23 : ordinaryBindings polynomial_23 witness_23 := by
 decide +kernel
theorem positive_23 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 9, evaluate (coefficient polynomial_23 k) ρ*u^k :=
 ordinary_slice_pos _ _ bound_23 ρ hρ u
end R7.Core.SpectralSliceCertificates.CriticalQ8003
