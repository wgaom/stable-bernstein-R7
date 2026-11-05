import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal045
import R7.Certificates.Spectral.Terminal.Terminal046

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry030
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_180 : BiPoly := [[6729517322519277600,389335390441844805250,1264334570488808484000],[0,0,0],[67997004857740288800,6364054140630174557000,16042718803901916492000],[0,0,0],[277010227994487094800,36063989682361519440000,65436660998625647907000],[0,0,0],[575854244198990460000,82595556865471533300000,115179539292121828275000],[0,0,0],[636320228098720006800,81054375665317825995000,88350369436070508312000],[0,0,0],[347748467639688334800,29320447477445407332000,23109655162859166132000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
def witness_180 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_0, 115000, by norm_num, R7.Core.Certificates.Terminal045.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_1, 2254000000, by norm_num, R7.Core.Certificates.Terminal045.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_2, 784000000, by norm_num, R7.Core.Certificates.Terminal045.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_3, 10584000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_4, 13335840000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_5, 51720121555200000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_6, 72115626688129753344000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_6⟩
theorem bound_180 : minorBindings polynomial_180 witness_180 := by
 decide +kernel
theorem positive_180 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_180 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_180 ρ hρ u
def polynomial_181 : BiPoly := [[231454348045069824,10721034003234676510,34891460497703024160],[0,6850996990748252400,10106055009461880000],[2642052612688567056,211125720194562447340,556853951686509095040],[0,42549510787568432400,70877667105939060000],[12193215711524421840,1485451124249699748000,2699372008747422840600],[0,58802056226234636400,171627479243126190000],[29017561408131543120,4062918036747151193400,5611269212145512200800],[0,248437228980137400,160134262328038320000],[37089970673649616800,4682545896339278730000,5090167997096201712000],[0,-10811780047364688000,41486048135532000000],[23671299200736679632,1995848003727862814880,1573078281261290606880],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
def witness_181 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_8, 1209800, by norm_num, R7.Core.Certificates.Terminal045.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_9, 36800, by norm_num, R7.Core.Certificates.Terminal045.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_10, 128, by norm_num, R7.Core.Certificates.Terminal045.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_11, 13824000, by norm_num, R7.Core.Certificates.Terminal045.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_12, 4354560000000, by norm_num, R7.Core.Certificates.Terminal045.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_13, 11851370496000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_14, 1321990721959270809600000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_14⟩
theorem bound_181 : minorBindings polynomial_181 witness_181 := by
 decide +kernel
theorem positive_181 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_181 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_181 ρ hρ u
def polynomial_182 : BiPoly := [[1401377551091936640,70096770907549959850,227239428433728447600],[0,30251410713132597000,13739025988098900000],[15528854610120924000,1307044333216415402500,3393691142777452597500],[0,154003049540733482400,94823129884471560000],[69851831046244299360,8700169565784596243250,15802377074782290504900],[0,185669073774405873000,210105924931118925000],[161548141472455982400,22811315083346953345500,31612799180505706191000],[0,29079010692687406500,144934139480816700000],[200080600693268762880,25344224236864513512000,27578613763652940979200],[0,-1081178004736468800,4148604813553200000],[123237176251257971280,10390755070954337335200,8189737443679915015200],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_182 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal045.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_17, 23000000, by norm_num, R7.Core.Certificates.Terminal045.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_18, 250000000, by norm_num, R7.Core.Certificates.Terminal045.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_19, 67500000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_20, 2126250000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_21, 28934010000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_22, 16137582055166880000000000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_22⟩
theorem bound_182 : minorBindings polynomial_182 witness_182 := by
 decide +kernel
theorem positive_182 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_182 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_182 ρ hρ u
def polynomial_183 : BiPoly := [[3736048358758685760,202131588186809836150,655874964401543318400],[0,40444605767084598000,-67200721599677400000],[39930891507077217120,3560226511301345859300,9095472166194802428300],[0,135720220896467781000,-424276195185734850000],[172136760506723844720,21973530912711028816500,39887951668958155024800],[0,108210824339190597000,-987654599038631925000],[380132457415053404400,54160525039960608070500,75326605498901900421000],[0,105211749968201992500,-964818566002194750000],[447718460226584702400,56901776386010193540000,61981228469023014816000],[0,84331884369444566400,-323591175457149600000],[261116393245239661920,22016055298853744452800,17352512999480215972800],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
def witness_183 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal045.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal045.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal045.polynomial_25, 8280000, by norm_num, R7.Core.Certificates.Terminal045.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal045.polynomial_26, 144000, by norm_num, R7.Core.Certificates.Terminal045.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal045.polynomial_27, 38880000000, by norm_num, R7.Core.Certificates.Terminal045.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal045.polynomial_28, 18370800000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal045.polynomial_29, 499979692800000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal045.polynomial_30, 557714835826567372800000000000000000, by norm_num, R7.Core.Certificates.Terminal045.positive_30⟩
theorem bound_183 : minorBindings polynomial_183 witness_183 := by
 decide +kernel
theorem positive_183 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_183 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_183 ρ hρ u
def polynomial_184 : BiPoly := [[274247226993087360,14431395299821089525,46670259063156962400],[0,4374639412087322000,-3842037178518600000],[2974574359466502120,259743344243336428050,667185421187059953300],[0,15876424190604133800,-27457012626792030000],[13122930589144414920,1662180585053448957750,3017982350971244467800],[0,12887977736273094000,-72987591058898850000],[29668079317375708200,4218006663826358454000,5861542050047308563000],[0,9485972540079021000,-85133838779759700000],[35785224669714906960,4545953165338772229000,4951064590304145566400],[0,8649424037891750400,-33188838508425600000],[21352976083138757400,1800378353878226766000,1419013913508896166000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_184 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_0, 103500, by norm_num, R7.Core.Certificates.Terminal046.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_1, 230000, by norm_num, R7.Core.Certificates.Terminal046.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_2, 18000, by norm_num, R7.Core.Certificates.Terminal046.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_3, 9720000000, by norm_num, R7.Core.Certificates.Terminal046.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_4, 612360000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_5, 479147205600000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_6, 44539726472260588800000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_6⟩
theorem bound_184 : minorBindings polynomial_184 witness_184 := by
 decide +kernel
theorem positive_184 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_184 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_184 ρ hρ u
def polynomial_185 : BiPoly := [[1404252883551372480,77600912047230781450,252503305581357823200],[0,11152387320509512000,-68608025543640600000],[14846946728084585280,1349564245727442881700,3430585129210707287700],[0,2120004854040725400,-430705511827947990000],[63122175272716010640,8135055027752562348000,14763855172764793332600],[0,-37378086506603829000,-965597320790185275000],[137072190586382647200,19608202151476455181500,27313691450971377573000],[0,66756975881670931500,-878077434463919550000],[158152807757838761280,20134809837874727352000,21943689180715516435200],[0,67753821630152044800,-259979234982667200000],[89885861226165054960,7578735546801678386400,5973372854961258146400],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_185 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal046.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal046.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal046.polynomial_9, 920000, by norm_num, R7.Core.Certificates.Terminal046.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal046.polynomial_10, 48000, by norm_num, R7.Core.Certificates.Terminal046.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal046.polynomial_11, 12960000000, by norm_num, R7.Core.Certificates.Terminal046.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal046.polynomial_12, 1224720000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal046.polynomial_13, 5555329920000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal046.polynomial_14, 2065610503061360640000000000000000, by norm_num, R7.Core.Certificates.Terminal046.positive_14⟩
theorem bound_185 : minorBindings polynomial_185 witness_185 := by
 decide +kernel
theorem positive_185 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_185 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_185 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry030
