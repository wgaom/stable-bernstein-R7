import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal054
import R7.Certificates.Spectral.Terminal.Terminal055

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry036
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_216 : BiPoly := [[326325446797179600,14787489661014394625,44905751562333414000],[0,3520805179197955000,16347306307783500000],[3898580489176648500,293164429547062740000,783114287032208677500],[0,39789166842280050000,128096573205532500000],[19139092141147612200,2266865009662416376875,4121445489253873848000],[0,78070282590402450000,362363099735098125000],[48617202584013129000,6734005543710694642500,9258399704836640610000],[0,-11991212940451500000,427223859975675000000],[66630006605429845200,8372300127854095755000,9087907111679701368000],[0,-42045811295307120000,161334631638180000000],[45756377321011623000,3857953615453343070000,3040744100376206070000],[0,0,0],[11784476524063458600,-49642777934956206000,59182299339899274000]]
def witness_216 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_0, 57500, by norm_num, R7.Core.Certificates.Terminal054.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_1, 57500000, by norm_num, R7.Core.Certificates.Terminal054.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_2, 750000000, by norm_num, R7.Core.Certificates.Terminal054.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_3, 1012500000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_4, 11481750000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_5, 5859137025000000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_6, 1361608485904705500000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_6⟩
theorem bound_216 : minorBindings polynomial_216 witness_216 := by
 decide +kernel
theorem positive_216 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_216 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_216 ρ hρ u
def polynomial_217 : BiPoly := [[22011165723957120,802798139732570050,2107627977654340800],[0,737330461564494000,2312339598982800000],[286746978045234600,17366996958500209000,49364764755763239000],[0,8160604374762901800,19989207755654670000],[1515241772068510080,163693952672433309750,298122718618088782200],[0,17306971534826208000,63231615836169300000],[4170866805971823600,557613413907984342000,755046325600655724000],[0,-1048213468095282000,83660858254337400000],[6232622965826158080,771148399824822492000,833039422156919347200],[0,-9301563151859779200,35691171570568800000],[4706370238732624080,396818086160915287200,312762250324409767200],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_217 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_8, 23000, by norm_num, R7.Core.Certificates.Terminal054.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_9, 9200000, by norm_num, R7.Core.Certificates.Terminal054.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_10, 16000000, by norm_num, R7.Core.Certificates.Terminal054.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_11, 5760000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_12, 311040000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_13, 16325867520000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_14, 433597540001218560000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_14⟩
theorem bound_217 : minorBindings polynomial_217 witness_217 := by
 decide +kernel
theorem positive_217 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_217 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_217 ρ hρ u
def polynomial_218 : BiPoly := [[158936480430194880,6228960811260483700,16424620532127589200],[0,4127610777515642000,12578852564802900000],[2039176911450449160,128611471805581339900,360117047595847649400],[0,44096285112651660900,107761355341913835000],[10726852706296831440,1176843818809993371750,2142892713175875017100],[0,91723692103276194000,337010777351464275000],[29384872312031942400,3951547167188618230500,5365255537508537466000],[0,-5884755057199746000,440790698515192200000],[43745641300462631040,5427749383065570456000,5868542778296203353600],[0,-48412748434310769600,185765304429104400000],[32944591671128368560,2777726603126407010400,2189335752270868370400],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_218 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal054.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal054.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal054.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_19, 1440000000, by norm_num, R7.Core.Certificates.Terminal054.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_20, 725760000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_21, 266655836160000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_22, 49574652073472655360000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_22⟩
theorem bound_218 : minorBindings polynomial_218 witness_218 := by
 decide +kernel
theorem positive_218 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_218 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_218 ρ hρ u
def polynomial_219 : BiPoly := [[542148892696385280,22741065102541354700,62736962459839975200],[0,8986091053350336000,28399802994425700000],[6833481636612234600,462476773148632274000,1267956610484237176500],[0,93135031517014908300,236663428537407645000],[35231407815877897680,3978499321786834686000,7240650606517833353700],[0,187337742881596308000,717075449611460550000],[94505319480168151200,12848701313157848131500,17529269388516271683000],[0,-14913342577204879500,908041385476105650000],[137628713313921977280,17157806722206362772000,18578862180884561875200],[0,-96224842421545723200,369225828406234800000],[101274115137172392240,8538937335536732661600,6730180275499336101600],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_219 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal054.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal054.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal054.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal054.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal054.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal054.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal054.polynomial_27, 540000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal054.polynomial_28, 17010000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal054.polynomial_29, 231472080000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal054.polynomial_30, 129100656441335040000000000000000000, by norm_num, R7.Core.Certificates.Terminal054.positive_30⟩
theorem bound_219 : minorBindings polynomial_219 witness_219 := by
 decide +kernel
theorem positive_219 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_219 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_219 ρ hρ u
def polynomial_220 : BiPoly := [[1131294598695273600,50547818191460795250,148301058623944374000],[0,5260360958017480000,31141112766651000000],[13814919476508083400,1011590581964052788500,2716209304833911818500],[0,69304633357119009000,245867208815885850000],[68990342780673090000,8065329464498722755000,14668502307436341225000],[0,145703793783853890000,706130256889128375000],[178763694585170958000,24633926591414019210000,33799426519234891095000],[0,-24981993350442922500,852418951348245750000],[250687153564983576000,31433835265152371100000,34098503154335655840000],[0,-87695549273069136000,336497945988204000000],[176924658974578275600,14917420646419593204000,11757543854787996804000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
def witness_220 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_0, 345000, by norm_num, R7.Core.Certificates.Terminal055.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_1, 23000000, by norm_num, R7.Core.Certificates.Terminal055.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_2, 2000000, by norm_num, R7.Core.Certificates.Terminal055.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_3, 1800000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_4, 6378750000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_5, 434010150000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_6, 403439551379172000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_6⟩
theorem bound_220 : minorBindings polynomial_220 witness_220 := by
 decide +kernel
theorem positive_220 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_220 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_220 ρ hρ u
def polynomial_221 : BiPoly := [[81897400396344960,3419167322196488525,9047922610337396400],[0,1546954162039913000,4485663968363100000],[1035562488292128060,67826982450830608400,187340370950676312900],[0,15534169800981504600,37799128197122490000],[5423506504057046160,603914984456476787625,1099463198012564279400],[0,31149291731384466000,115700121924871725000],[14786838491130559800,1999900218510673033500,2722593397906242432000],[0,-2216007918866259000,147977694625011300000],[21931460920071077760,2728729983678691734000,2952904800746985638400],[0,-15857277402801542400,60846203932113600000],[16472295835564184280,1388863301563203505200,1094667876135434185200],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_221 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal055.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal055.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal055.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal055.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal055.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal055.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal055.polynomial_11, 4320000000, by norm_num, R7.Core.Certificates.Terminal055.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal055.polynomial_12, 544320000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal055.polynomial_13, 99995938560000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal055.polynomial_14, 9295247263776122880000000000000000, by norm_num, R7.Core.Certificates.Terminal055.positive_14⟩
theorem bound_221 : minorBindings polynomial_221 witness_221 := by
 decide +kernel
theorem positive_221 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_221 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_221 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry036
