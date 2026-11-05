import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal028
import R7.Certificates.Spectral.Terminal.Terminal029

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry019
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_114 : BiPoly := [[710752439153993760,47143451175790836150,153474437289186788400],[0,393341911030008000,78876722431952100000],[6020508126711384540,618184929516806145600,1522008238860596321100],[0,29245530187886682600,357886933978935690000],[19966976254515689280,2701748204432519604750,4897473136786805222700],[0,36408267065396025000,549298363019124375000],[33238203990800149800,4833733030522614463500,6776509256352488907000],[0,-24202061922564900000,333616775703873750000],[29154685587118933680,3733111932176213577000,4075551778717837051200],[0,-17221621075445181600,66081348101597400000],[12593898138830818140,1061855804634301092600,836928614294022432600],[0,0,0],[2020195975553735760,-8510190503135349600,10145537029697018400]]
def witness_114 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_16, 1863000, by norm_num, R7.Core.Certificates.Terminal028.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_17, 74520000, by norm_num, R7.Core.Certificates.Terminal028.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_18, 104976000, by norm_num, R7.Core.Certificates.Terminal028.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_19, 1049760000000, by norm_num, R7.Core.Certificates.Terminal028.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_20, 37791360000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_21, 18366600960000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_22, 731695848752056320000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_22⟩
theorem bound_114 : minorBindings polynomial_114 witness_114 := by
 decide +kernel
theorem positive_114 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_114 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_114 ρ hρ u
def polynomial_115 : BiPoly := [[29348220965276160,545548781406858400,2769642149353454400],[0,1504500586691984000,6251721281470800000],[333097859427888960,17810798368006414400,55171327303403231400],[0,16285509410387094000,44630372281841100000],[1523388233208663360,160004437776128547000,291113867931105452400],[0,29614778184291237000,113224320755524575000],[3570124673424441600,471519102782315569500,634155360643382094000],[0,-1445166250412913000,117748594953842850000],[4492263528796071600,552508714857658005000,595726231511590344000],[0,-10065252377427602400,38621535288078600000],[2832537643681671900,238825700004254571000,188236539547098471000],[0,0,0],[673398658517911920,-2836730167711783200,3381845676565672800]]
def witness_115 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal028.polynomial_24, 368000, by norm_num, R7.Core.Certificates.Terminal028.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal028.polynomial_25, 88320000, by norm_num, R7.Core.Certificates.Terminal028.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal028.polynomial_26, 128000, by norm_num, R7.Core.Certificates.Terminal028.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal028.polynomial_27, 11520000000, by norm_num, R7.Core.Certificates.Terminal028.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal028.polynomial_28, 3110400000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal028.polynomial_29, 7558272000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal028.polynomial_30, 100369800926208000000000000000000, by norm_num, R7.Core.Certificates.Terminal028.positive_30⟩
theorem bound_115 : minorBindings polynomial_115 witness_115 := by
 decide +kernel
theorem positive_115 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_115 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_115 ρ hρ u
def polynomial_116 : BiPoly := [[239544938689551360,5604726945617446400,25359909365891222400],[0,12538128658513506000,45286471968217200000],[2708776932328681920,159085071449912733800,473708555937545572800],[0,120572829247326739800,318746858426234370000],[12309302782771606080,1334408583860514336000,2427550930948241797200],[0,209421034027660962000,798330806954968950000],[28715473935764859600,3838246225252361937000,5191739020258807464000],[0,-10991146858235082000,817814596144847400000],[36013502863019695680,4453045186481668512000,4809477803992202131200],[0,-68852161190519251200,264193690666276800000],[22660301149453375200,1910605600034036568000,1505892316376787768000],[0,0,0],[5387189268143295360,-22693841341694265600,27054765412525382400]]
def witness_116 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_0, 1472000, by norm_num, R7.Core.Certificates.Terminal029.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_1, 14720000, by norm_num, R7.Core.Certificates.Terminal029.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_2, 128000, by norm_num, R7.Core.Certificates.Terminal029.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_3, 69120000000, by norm_num, R7.Core.Certificates.Terminal029.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_4, 7464960000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_5, 145118822400000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_6, 15416801422265548800000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_6⟩
theorem bound_116 : minorBindings polynomial_116 witness_116 := by
 decide +kernel
theorem positive_116 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_116 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_116 ρ hρ u
def polynomial_117 : BiPoly := [[941126058791896320,27900137901603459300,115630544217008368800],[0,46806351349813744000,154271286469770300000],[10437066262073854080,686897500998568266200,1958144247799159979700],[0,399334966286709847800,1049512350442052070000],[46556346544214315760,5262287850263180535750,9569245363381765418400],[0,649295011362658401000,2532268142297403975000],[106597400405300454600,14477630220457692349500,19726139637577459764000],[0,-40664926960670439000,2490975775480474800000],[131178283631548130880,16334441694990982332000,17680817895346078099200],[0,-200858847102152870400,770718583140105600000],[80937947438945004240,6824291284224135741600,5378738453109911181600],[0,0,0],[18855162438501533760,-79428444695929929600,94691678943838838400]]
def witness_117 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_8, 138000, by norm_num, R7.Core.Certificates.Terminal029.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_9, 1840000, by norm_num, R7.Core.Certificates.Terminal029.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal029.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_11, 1440000000, by norm_num, R7.Core.Certificates.Terminal029.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_12, 181440000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_13, 823011840000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_14, 306016370823905280000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_14⟩
theorem bound_117 : minorBindings polynomial_117 witness_117 := by
 decide +kernel
theorem positive_117 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_117 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_117 ρ hρ u
def polynomial_118 : BiPoly := [[2287178247388481280,84236907411021920950,325748922356904115200],[0,98426667931349992000,322105084323485400000],[24689569483160555760,1824980081673822453900,4991542461275190930900],[0,754111441173490453200,2079461776365563580000],[106971181231352719680,12654644284768577376000,22997478057050035771200],[0,1132044702117202908000,4729441204326433050000],[237516275148304917600,32836063141137103227000,45089078417274080934000],[0,-96031254913509573000,4358240740728611100000],[282822021437173283520,35489868010847965008000,38507305771980258796800],[0,-328678113439886515200,1261175863320172800000],[168383468541322772640,14197269304868302497600,11189938289384438337600],[0,0,0],[37710324877003067520,-158856889391859859200,189383357887677676800]]
def witness_118 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_16, 23000, by norm_num, R7.Core.Certificates.Terminal029.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_17, 21160000, by norm_num, R7.Core.Certificates.Terminal029.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_18, 1104000, by norm_num, R7.Core.Certificates.Terminal029.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_19, 596160000000, by norm_num, R7.Core.Certificates.Terminal029.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_20, 37558080000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_21, 3066542115840000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_22, 2280433995379742146560000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_22⟩
theorem bound_118 : minorBindings polynomial_118 witness_118 := by
 decide +kernel
theorem positive_118 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_118 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_118 ρ hρ u
def polynomial_119 : BiPoly := [[3760984431639655200,168189656993844891750,612822564755478468000],[0,122279089401888830000,451795134449646000000],[39097754054427980700,3221406721111211785500,8492566046411950263000],[0,860854571633037093000,2721280294613295450000],[162807025885963300800,20133039151244082232500,36560826815198134572000],[0,1183988398053832650000,5719309986775533750000],[346327839413565723000,48715366416378577785000,67385168566421145570000],[0,-153892413687905392500,4832231690297781000000],[393622811299404036000,49755382928668081350000,54107055661353312240000],[0,-335765835915381144000,1288372272653466000000],[222681036295589898600,18775374261872936274000,14798287955164202874000],[0,0,0],[47137906096253834400,-198571111739824824000,236729197359597096000]]
def witness_119 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal029.polynomial_24, 1035000, by norm_num, R7.Core.Certificates.Terminal029.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal029.polynomial_25, 23000000, by norm_num, R7.Core.Certificates.Terminal029.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal029.polynomial_26, 6000000, by norm_num, R7.Core.Certificates.Terminal029.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal029.polynomial_27, 5400000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal029.polynomial_28, 6378750000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal029.polynomial_29, 217005075000000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal029.polynomial_30, 201719775689586000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal029.positive_30⟩
theorem bound_119 : minorBindings polynomial_119 witness_119 := by
 decide +kernel
theorem positive_119 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_119 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_119 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry019
