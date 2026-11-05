import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal018
import R7.Certificates.Spectral.Terminal.Terminal019

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry012
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_72 : BiPoly := [[600250438256019840,34381450245034896600,112666374919879185600],[0,10493417322793582000,-5308526263656600000],[5205963400492478400,486616010259238166000,1227692514376746306000],[0,31023350406244962600,-41690734370019810000],[18237211005756476160,2376569752230623907000,4312283982935053604400],[0,21573985421917296000,-99504836479969650000],[32817684498016982400,4712180863167347148000,6573990860741591316000],[0,11114654496658713000,-88167369190071600000],[31590351080820486720,4027062079261656828000,4390572844789955884800],[0,6555714250941763200,-25155032361544800000],[15106867432968916800,1273737066689357712000,1003928210917858512000],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_72 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_0, 276000, by norm_num, R7.Core.Certificates.Terminal018.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_1, 73600000, by norm_num, R7.Core.Certificates.Terminal018.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_2, 128000000, by norm_num, R7.Core.Certificates.Terminal018.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_3, 92160000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_4, 1866240000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_5, 24186470400000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_6, 1284733451855462400000000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_6⟩
theorem bound_72 : minorBindings polynomial_72 witness_72 := by
 decide +kernel
theorem positive_72 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_72 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_72 ρ hρ u
def polynomial_73 : BiPoly := [[897103727343982080,55787354436120314200,180356449929270187200],[0,6563884044685430000,-24569973170334000000],[7302489707551974480,716864600654915572200,1783592495397972628200],[0,8272275895314609300,-133521399891929205000],[23998116775368204000,3186645224606880360000,5779577195389615860000],[0,-1517914313661672000,-238349420995234950000],[40352707246254145200,5829443193456634824000,8152061911266379518000],[0,14249427428094043500,-165526732850287950000],[36214555216756023360,4625714690546728284000,5046292401779635142400],[0,9782086709520432000,-37534995932148000000],[16152727486020611040,1361918863614005553600,1073430933212171793600],[0,0,0],[2693594634071647680,-11346920670847132800,13527382706262691200]]
def witness_73 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_8, 92000, by norm_num, R7.Core.Certificates.Terminal018.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_9, 7360000, by norm_num, R7.Core.Certificates.Terminal018.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_10, 384000, by norm_num, R7.Core.Certificates.Terminal018.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_11, 138240000000, by norm_num, R7.Core.Certificates.Terminal018.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_12, 466560000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_13, 604661760000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_14, 32118336296386560000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_14⟩
theorem bound_73 : minorBindings polynomial_73 witness_73 := by
 decide +kernel
theorem positive_73 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_73 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_73 ρ hρ u
def polynomial_74 : BiPoly := [[745405152759953280,49299581409145574700,157868299974026095200],[0,270570347621833000,-28795991067657900000],[5600862435097239840,567270508621186622600,1399165497406699860600],[0,-8804158762080797700,-124829251586758755000],[16818369023846446560,2257273716317280649500,4093002199180389065400],[0,-11023266855283758000,-184127466691402425000],[25814747638607500800,3741130972969910586000,5238228882700376622000],[0,8094202433120695500,-108609842232390600000],[21219400500588250560,2713003861309653204000,2960542352144720390400],[0,5526020913097507200,-21203980158160800000],[8715500442097452000,734848307705398680000,579189352452610680000],[0,0,0],[1346797317035823840,-5673460335423566400,6763691353131345600]]
def witness_74 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_16, 138000, by norm_num, R7.Core.Certificates.Terminal018.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_17, 3680000, by norm_num, R7.Core.Certificates.Terminal018.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_18, 128000, by norm_num, R7.Core.Certificates.Terminal018.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_19, 46080000000, by norm_num, R7.Core.Certificates.Terminal018.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_20, 51840000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_21, 5038848000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_22, 133826401234944000000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_22⟩
theorem bound_74 : minorBindings polynomial_74 witness_74 := by
 decide +kernel
theorem positive_74 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_74 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_74 ρ hρ u
def polynomial_75 : BiPoly := [[33016748585935680,1827176067094500700,6016300985598511200],[0,735480846643114000,-176849421748200000],[291460626999402840,26720969901075517600,67777122620952030600],[0,2247214717255077600,-1956086246707560000],[1046989974450116340,135561739252126795500,246022886893865970600],[0,1549776422648484000,-5649027948329850000],[1930956854616585000,276846806859037965000,386010008852727150000],[0,735553924365852000,-5851596939273900000],[1903714474440852720,242631273966400728000,264516463647550324800],[0,480523557660652800,-1843824361579200000],[929653380490394880,78383819488575859200,61780197594945139200],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
def witness_75 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal018.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal018.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal018.polynomial_25, 3680000, by norm_num, R7.Core.Certificates.Terminal018.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal018.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal018.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal018.polynomial_27, 576000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal018.polynomial_28, 373248000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal018.polynomial_29, 3869835264000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal018.polynomial_30, 12847334518554624000000000000000000, by norm_num, R7.Core.Certificates.Terminal018.positive_30⟩
theorem bound_75 : minorBindings polynomial_75 witness_75 := by
 decide +kernel
theorem positive_75 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_75 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_75 ρ hρ u
def polynomial_76 : BiPoly := [[170437810267938240,10070507951939492600,32806284299305341600],[0,2525636116463600000,-6410228632042500000],[1463195196189724500,139704676206183942500,350353394585108955000],[0,4613395316271041100,-35944655630005035000],[5054200265703430800,665214459938190915000,1206741630330888147000],[0,984545658464733000,-69336322781381325000],[8933893714026066600,1287935457999236194500,1799593079761359594000],[0,4640790330914629500,-52269146602293150000],[8406501540600201120,1073385863554069863000,1170853523932126780800],[0,3303599458916988000,-12676292485857000000],[3907449364873690980,329456991287920408200,259669893016253788200],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_76 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_0, 92000, by norm_num, R7.Core.Certificates.Terminal019.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_1, 92000000, by norm_num, R7.Core.Certificates.Terminal019.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_2, 250000000, by norm_num, R7.Core.Certificates.Terminal019.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_3, 22500000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_4, 20958750000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_5, 147622500000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_6, 1960347674340000000000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_6⟩
theorem bound_76 : minorBindings polynomial_76 witness_76 := by
 decide +kernel
theorem positive_76 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_76 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_76 ρ hρ u
def polynomial_77 : BiPoly := [[374115455260906320,23548502722294089300,76270770269481268800],[0,2367519282687384000,-22437996767674200000],[3017913742906215660,299555445745798074900,743464561810906634400],[0,-2518595367126786000,-110336430391155900000],[9810375828029587440,1310239447510166673000,2375957306668762119600],[0,-7666798906621710000,-182356837473534750000],[16254365700639164400,2353877412604168810500,3294721740750725196000],[0,9212238672807114000,-118223093834997300000],[14309272988577696600,1829635359849620257500,1996615161319871844000],[0,6487068028418812800,-24891628881319200000],[6231582816099678180,525416540009360056200,414120387003616636200],[0,0,0],[1010097987776867880,-4255095251567674800,5072768514848509200]]
def witness_77 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal019.polynomial_8, 138000, by norm_num, R7.Core.Certificates.Terminal019.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal019.polynomial_9, 49680000, by norm_num, R7.Core.Certificates.Terminal019.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal019.polynomial_10, 1296000, by norm_num, R7.Core.Certificates.Terminal019.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal019.polynomial_11, 349920000000, by norm_num, R7.Core.Certificates.Terminal019.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal019.polynomial_12, 94478400000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal019.polynomial_13, 45916502400000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal019.polynomial_14, 914619810940070400000000000000000, by norm_num, R7.Core.Certificates.Terminal019.positive_14⟩
theorem bound_77 : minorBindings polynomial_77 witness_77 := by
 decide +kernel
theorem positive_77 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_77 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_77 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry012
