import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal006
import R7.Certificates.Spectral.Terminal.Terminal007

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry004
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_24 : BiPoly := [[9637321208867712,647854202643230880,2137911477015214080],[0,29400786167940000,1206775028178000000],[55149692763768408,5761696173854793120,14140021685283486720],[0,342759798576262800,3629513967146820000],[128306762957414160,17502154237602972000,31717895076941774400],[0,278928632131034400,3843892202088240000],[154476548369326800,22530334932735876000,31619339776669212000],[0,-118028988577659600,1664989174436220000],[100526176868163840,12885484071044016000,14071949015924505600],[0,-62925703979371200,241453190206800000],[32925223892368152,2776093606887061680,2188048664820973680],[0,0,0],[4081203991017648,-17192304046738080,20496034403428320]]
def witness_24 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_0, 17884800, by norm_num, R7.Core.Certificates.Terminal006.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_1, 7726233600, by norm_num, R7.Core.Certificates.Terminal006.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_2, 544195584, by norm_num, R7.Core.Certificates.Terminal006.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_3, 1763193692160000, by norm_num, R7.Core.Certificates.Terminal006.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_4, 95212459376640000000, by norm_num, R7.Core.Certificates.Terminal006.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_5, 2056589122535424000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_6, 165517583124246980198400000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_6⟩
theorem bound_24 : minorBindings polynomial_24 witness_24 := by
 decide +kernel
theorem positive_24 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_24 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_24 ρ hρ u
def polynomial_25 : BiPoly := [[2538224515915776,4194477691966240,127195300246179840],[0,69397305403116800,658166307428160000],[23882488034452416,854795109583540240,3195596947805002440],[0,1287106409445280800,3944579412818520000],[92326559588403840,8693593407437493000,15810511524590595600],[0,2269898179753406400,8581268923061940000],[185371858043192160,23613194911286738700,31185001997066804400],[0,-63633145678727400,7684513686724680000],[201052353736327680,24383387513092707000,26172827190329011200],[0,-560610817270761600,2151128421842400000],[109427949995223564,9226428752301116760,7272044091905000760],[0,0,0],[22446621950597064,-94557672257059440,112728189218855760]]
def witness_25 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_8, 73600, by norm_num, R7.Core.Certificates.Terminal006.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_9, 1177600, by norm_num, R7.Core.Certificates.Terminal006.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_10, 1024, by norm_num, R7.Core.Certificates.Terminal006.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_11, 18432000, by norm_num, R7.Core.Certificates.Terminal006.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_12, 995328000000, by norm_num, R7.Core.Certificates.Terminal006.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_13, 10749542400000000, by norm_num, R7.Core.Certificates.Terminal006.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_14, 4758272043909120000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_14⟩
theorem bound_25 : minorBindings polynomial_25 witness_25 := by
 decide +kernel
theorem positive_25 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_25 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_25 ρ hρ u
def polynomial_26 : BiPoly := [[23002659675486720,110921985328062800,1353932323416004800],[0,764612203749916000,5713739805409200000],[219970284527851200,8756518194060938000,31036364160643233000],[0,11511261360871258800,34434446236214220000],[860809393809529920,83321604635943421500,151556279958624817800],[0,19899094790817306000,75464634461260725000],[1750734214852370400,225043800718015525500,298597549304439486000],[0,-626879051693532000,68416737528531150000],[1928846018657893680,234751999952199132000,252265884169371451200],[0,-5085540985241908800,19513807826713200000],[1070069776501964940,90223042223829504600,71111581606681644600],[0,0,0],[224466219505970640,-945576722570594400,1127281892188557600]]
def witness_26 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_16, 184000, by norm_num, R7.Core.Certificates.Terminal006.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_17, 73600000, by norm_num, R7.Core.Certificates.Terminal006.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_18, 16000000, by norm_num, R7.Core.Certificates.Terminal006.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_19, 1440000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_20, 311040000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_21, 16796160000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_22, 74348000686080000000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_22⟩
theorem bound_26 : minorBindings polynomial_26 witness_26 := by
 decide +kernel
theorem positive_26 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_26 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_26 ρ hρ u
def polynomial_27 : BiPoly := [[103908566120302080,1015069519982256700,7781760206395987200],[0,4070988147602694000,23973258805372800000],[989866280375330400,45749964624802198500,151499381542631923500],[0,48707523964364935200,142507222177916880000],[3861422580432654720,390151453478898944625,709672506255315424800],[0,80120540619701226000,307897063816905225000],[7835393814510853800,1022207972804792833500,1366340553812194204500],[0,-3077805611167389000,275846609131546050000],[8626402552499309520,1056245226078964698000,1137247598248141636800],[0,-20387928089316268800,78230833627003200000],[4793525243153598600,404166569237969274000,318554143848935874000],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
def witness_27 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal006.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal006.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal006.polynomial_25, 27600000, by norm_num, R7.Core.Certificates.Terminal006.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal006.polynomial_26, 54000000, by norm_num, R7.Core.Certificates.Terminal006.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal006.polynomial_27, 4860000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal006.polynomial_28, 262440000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal006.polynomial_29, 14030042400000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal006.polynomial_30, 279467164453910400000000000000000000, by norm_num, R7.Core.Certificates.Terminal006.positive_30⟩
theorem bound_27 : minorBindings polynomial_27 witness_27 := by
 decide +kernel
theorem positive_27 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_27 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_27 ρ hρ u
def polynomial_28 : BiPoly := [[301017563684386560,4754281717097516900,28539847539347390400],[0,12921809047538685000,63858193536784500000],[2831331805137056160,153452985579265602400,475544154015643154400],[0,126156000417191349600,368093200049296740000],[10892497416146614800,1158868557845595495000,2107505330638879707000],[0,193682134133048304000,769266899564760900000],[21789775350540041400,2896537582609072308000,3906564474485530251000],[0,-9852608796252223500,665890686987088950000],[23648783108235543360,2918823591389217084000,3150637863110351942400],[0,-47709124653450528000,183065418756792000000],[12957043990584878640,1092474484122026037600,861061503979547877600],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_28 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_0, 46000, by norm_num, R7.Core.Certificates.Terminal007.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_1, 180320000, by norm_num, R7.Core.Certificates.Terminal007.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_2, 1024000, by norm_num, R7.Core.Certificates.Terminal007.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_3, 184320000000, by norm_num, R7.Core.Certificates.Terminal007.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_4, 1244160000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_5, 806215680000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_6, 42824448395182080000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_6⟩
theorem bound_28 : minorBindings polynomial_28 witness_28 := by
 decide +kernel
theorem positive_28 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_28 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_28 ρ hρ u
def polynomial_29 : BiPoly := [[616312640270799360,14187689523640518275,72214923452899292400],[0,26300707165213301000,119292564646658700000],[5669079410239507980,358489289379268500950,1046534991822073393200],[0,217513365222820959600,657232992132618240000],[21303335317381666920,2394365714566696514625,4352387687468253397800],[0,307693982272188942000,1305253947191955075000],[41562773541813871800,5640498162683623768500,7679835553872411949500],[0,-22072481476063263000,1069150804706687850000],[43921562109981917760,5469725108995832034000,5920763680855351238400],[0,-72559057206758572800,278417478598459200000],[23386592852961496200,1971842959009486458000,1554158095747838658000],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_29 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal007.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal007.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal007.polynomial_9, 230000, by norm_num, R7.Core.Certificates.Terminal007.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal007.polynomial_10, 2000, by norm_num, R7.Core.Certificates.Terminal007.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal007.polynomial_11, 180000000, by norm_num, R7.Core.Certificates.Terminal007.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal007.polynomial_12, 158760000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal007.polynomial_13, 257191200000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal007.polynomial_14, 23907528970617600000000000000000, by norm_num, R7.Core.Certificates.Terminal007.positive_14⟩
theorem bound_29 : minorBindings polynomial_29 witness_29 := by
 decide +kernel
theorem positive_29 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_29 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_29 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry004
