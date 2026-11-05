import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal055
import R7.Certificates.Spectral.Terminal.Terminal056

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry037
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_222 : BiPoly := [[532878424249583520,22841205288248669175,62237501130578716800],[0,5709612126346797000,14389091814438900000],[6717342563769256020,458637981074448210300,1252009551313725616800],[0,52766729599409168400,119592947148474960000],[34697814611197857840,3930704620473764363625,7153756391394848955600],[0,99709938032324004000,358257931323255900000],[93278089123678499400,12699249957927597055500,17337356459455693221000],[0,-6048283274874823500,445150345036896450000],[136250666972687564640,16999730956702582956000,18412327760826708777600],[0,-45409476198931689600,174241402169234400000],[100664030106225570600,8487497953997354754000,6689637020827653354000],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_222 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_16, 103500, by norm_num, R7.Core.Certificates.Terminal055.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_17, 4140000, by norm_num, R7.Core.Certificates.Terminal055.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_18, 432000, by norm_num, R7.Core.Certificates.Terminal055.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_19, 116640000000, by norm_num, R7.Core.Certificates.Terminal055.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_20, 11022480000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_21, 1124954308800000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_22, 627429190304888294400000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_22⟩
theorem bound_222 : minorBindings polynomial_222 witness_222 := by
 decide +kernel
theorem positive_222 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_222 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_222 ρ hρ u
def polynomial_223 : BiPoly := [[1627041574460073600,72610142039403464000,210399901667600124000],[0,0,0],[19932188341473088200,1447119254712532198000,3891397635552769938000],[0,0,0],[100053817415720065800,11645029806762254786250,21181286046791030922000],[0,0,0],[260807905830213414000,35873421118743949155000,49184699250425823135000],[0,0,0],[368407495268306272800,46158494477714214120000,50059169159743768752000],[0,0,0],[262336563307133305200,22118934061932500268000,17433599508823581468000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
def witness_223 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_24, 1840000, by norm_num, R7.Core.Certificates.Terminal055.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_25, 36064000000, by norm_num, R7.Core.Certificates.Terminal055.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_26, 784000000, by norm_num, R7.Core.Certificates.Terminal055.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_27, 2116800000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_28, 10668672000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_29, 31213547043840000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_30, 43522413299502868684800000000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_30⟩
theorem bound_223 : minorBindings polynomial_223 witness_223 := by
 decide +kernel
theorem positive_223 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_223 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_223 ρ hρ u
def polynomial_224 : BiPoly := [[191457482040365760,8389135547772802400,23395822199711018400],[0,712499760151372000,621399939566400000],[2407103399261914560,170104689147970923400,459992292307797785400],[0,4109480130976436400,4130375038071660000],[12284863399351146240,1412639778069556000500,2570244531571437411600],[0,4174708558780404000,7438377032427150000],[32611715766857880000,4466366201597051970000,6113050843824643950000],[0,399826987815969000,811507441241700000],[46970856141649554240,5875694003777671836000,6369075572390501241600],[0,1441570672981958400,-5531473084737600000],[34164761733022011840,2880605366205162825600,2270422261614233865600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_224 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_0, 368000, by norm_num, R7.Core.Certificates.Terminal056.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_1, 88320000, by norm_num, R7.Core.Certificates.Terminal056.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal056.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_3, 1152000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_4, 979776000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_5, 53331167232000000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_6, 9914930414694531072000000000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_6⟩
theorem bound_224 : minorBindings polynomial_224 witness_224 := by
 decide +kernel
theorem positive_224 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_224 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_224 ρ hρ u
def polynomial_225 : BiPoly := [[3985805685148992,152454377144107455,374818462594829280],[0,110507050422337800,315402080328360000],[53971280525226348,3380145404324357220,9442803833693288820],[0,1157379328438685100,2780947505131065000],[287162755190403120,31340500010482987125,57081335124501843300],[0,2478394853219808000,8944802347535550000],[798128833241521800,107182092848089761000,145464971803149762000],[0,-160870547837583000,12072588713918100000],[1206314122417966080,149630518588145022000,161767533161622067200],[0,-1390086006089745600,5333920474568400000],[923843046862329912,77893920616772260080,61394071359976732080],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
def witness_225 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_8, 6900, by norm_num, R7.Core.Certificates.Terminal056.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_9, 165600, by norm_num, R7.Core.Certificates.Terminal056.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_10, 3456, by norm_num, R7.Core.Certificates.Terminal056.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_11, 42923520000, by norm_num, R7.Core.Certificates.Terminal056.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_12, 151165440000000, by norm_num, R7.Core.Certificates.Terminal056.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_13, 29386561536000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_14, 156095114400438681600000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_14⟩
theorem bound_225 : minorBindings polynomial_225 witness_225 := by
 decide +kernel
theorem positive_225 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_225 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_225 ρ hρ u
def polynomial_226 : BiPoly := [[27989874251680608,1132135806143297170,2764546304702334720],[0,515699568637576400,1471876374865680000],[370335686165818056,23361468836001199840,64997851634193560040],[0,5401103532713863800,12977755023944970000],[1977553441772208720,216537168949223405250,394383639803039659800],[0,11565842648359104000,41742410955165900000],[5509663558505989200,740890489426427574000,1006218212409080478000],[0,-750729223242054000,56338747331617800000],[8356238452166119200,1037433906808580610000,1121899442861172528000],[0,-6487068028418812800,24891628881319200000],[6426228992639854608,541828152214780626720,427055615875058274720],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_226 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_16, 4600, by norm_num, R7.Core.Certificates.Terminal056.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_17, 3606400, by norm_num, R7.Core.Certificates.Terminal056.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_18, 50176, by norm_num, R7.Core.Certificates.Terminal056.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_19, 18063360000, by norm_num, R7.Core.Certificates.Terminal056.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_20, 34139750400000000, by norm_num, R7.Core.Certificates.Terminal056.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_21, 30971581562880000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_22, 1151600806684520349696000000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_22⟩
theorem bound_226 : minorBindings polynomial_226 witness_226 := by
 decide +kernel
theorem positive_226 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_226 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_226 ρ hρ u
def polynomial_227 : BiPoly := [[93329325657481248,3949066420074925145,10144803740551792320],[0,773549352956364600,2207814562298520000],[1212219576318899988,80354179497910966820,220529063139076191420],[0,8101655299070795700,19466632535917455000],[6368495996314826640,711564423039721718625,1295457222482600210100],[0,17348763972538656000,62613616432748850000],[17447267935268965800,2363510092409718471000,3220150259217495222000],[0,-1126093834863081000,84508120997426700000],[26006959673934553440,3238609922939554506000,3505621627952988969600],[0,-9730602042628219200,37337443321978800000],[19644737996487656808,1656348085567968624720,1305492800428184472720],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
def witness_227 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal056.polynomial_24, 2300, by norm_num, R7.Core.Certificates.Terminal056.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal056.polynomial_25, 901600, by norm_num, R7.Core.Certificates.Terminal056.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal056.polynomial_26, 6272, by norm_num, R7.Core.Certificates.Terminal056.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal056.polynomial_27, 3386880000, by norm_num, R7.Core.Certificates.Terminal056.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal056.polynomial_28, 213373440000000, by norm_num, R7.Core.Certificates.Terminal056.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal056.polynomial_29, 290358577152000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal056.polynomial_30, 32388772688002134835200000000000, by norm_num, R7.Core.Certificates.Terminal056.positive_30⟩
theorem bound_227 : minorBindings polynomial_227 witness_227 := by
 decide +kernel
theorem positive_227 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_227 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_227 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry037
