import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal013
import R7.Certificates.Spectral.Terminal.Terminal014

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry009
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_54 : BiPoly := [[203677644992968080,13477994770354596700,43464485970175927200],[0,-54399567254992000,13398269027889600000],[1289575793044527660,131251613463039882400,323545879149589589400],[0,3423497713485765600,46016804820824640000],[3337163862475707180,449142807307181121000,814322595459260896200],[0,3464985055942044000,55884793248414900000],[4488401933175439800,651216397148201826000,912188418161706882000],[0,-2057728805681724000,27854543853474300000],[3274430781945295080,418854415353291499500,457137978554122927200],[0,-1218470449782369600,4675411774004400000],[1205644227823480860,101654015899246817400,80121193755944477400],[0,0,0],[168349664629477980,-709182541927945800,845461419141418200]]
def witness_54 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal013.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal013.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_18, 16000, by norm_num, R7.Core.Certificates.Terminal013.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_19, 2880000000, by norm_num, R7.Core.Certificates.Terminal013.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_20, 51840000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_21, 8398080000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_22, 27880500257280000000000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_22⟩
theorem bound_54 : minorBindings polynomial_54 witness_54 := by
 decide +kernel
theorem positive_54 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_54 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_54 ρ hρ u
def polynomial_55 : BiPoly := [[24430410965689344,684506363998002560,2856268153695480960],[0,1207816081052055600,3708572525712720000],[237567907290079296,15371031431345508440,44037748730891096640],[0,8700996614811263400,21762162216361710000],[942274005211062720,106220073730419654000,193201051320228394800],[0,12226253303051330400,46238159908543590000],[1946404509453517680,264472334452287687600,360480958829072071200],[0,-623120809559421600,40462162987834620000],[2186444346882563520,272488827022833528000,295026894383845996800],[0,-2917464457225392000,11194647909588000000],[1243411396405903152,104838358565970211680,82631014283239123680],[0,0,0],[269359463407164768,-1134692067084713280,1352738270626269120]]
def witness_55 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal013.polynomial_24, 294400, by norm_num, R7.Core.Certificates.Terminal013.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal013.polynomial_25, 588800, by norm_num, R7.Core.Certificates.Terminal013.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal013.polynomial_26, 1024, by norm_num, R7.Core.Certificates.Terminal013.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal013.polynomial_27, 73728000, by norm_num, R7.Core.Certificates.Terminal013.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal013.polynomial_28, 47775744000000, by norm_num, R7.Core.Certificates.Terminal013.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal013.polynomial_29, 6191736422400000000, by norm_num, R7.Core.Certificates.Terminal013.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal013.polynomial_30, 32889176367499837440000000000, by norm_num, R7.Core.Certificates.Terminal013.positive_30⟩
theorem bound_55 : minorBindings polynomial_55 witness_55 := by
 decide +kernel
theorem positive_55 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_55 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_55 ρ hρ u
def polynomial_56 : BiPoly := [[185766306758585856,6223173637460030440,24103809982740287040],[0,8657280538057561800,23097834566237160000],[1782387791202817152,124733041005588165280,346785400194903688680],[0,56278971062078615700,132755811196900455000],[6996452375868308640,811906103531736790500,1476271750855371402600],[0,74542093957491879600,274269183660388035000],[14283931505883751440,1962683764574528530800,2688524507454657969600],[0,-3350586513382693200,232018987589532990000],[15832872856735804800,1982841032055189600000,2150103989733037632000],[0,-15977408292216705600,61307160022508400000],[8866569116427141168,747585678372292257120,589228634561789265120],[0,0,0],[1885516243850153376,-7942844469592992960,9469167894383883840]]
def witness_56 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_0, 18400, by norm_num, R7.Core.Certificates.Terminal014.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_1, 147200, by norm_num, R7.Core.Certificates.Terminal014.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_2, 1024, by norm_num, R7.Core.Certificates.Terminal014.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_3, 73728000, by norm_num, R7.Core.Certificates.Terminal014.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_4, 1254113280000000, by norm_num, R7.Core.Certificates.Terminal014.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_5, 1137731567616000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_6, 42303703102696665907200000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_6⟩
theorem bound_56 : minorBindings polynomial_56 witness_56 := by
 decide +kernel
theorem positive_56 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_56 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_56 ρ hρ u
def polynomial_57 : BiPoly := [[660493610750958336,26360338943729074390,96597793136000610240],[0,26513814168774505200,65787636453775740000],[6200333834312902896,475637306671545929940,1280342169779725970640],[0,154882505919463354500,359226060560789175000],[23746934223546811200,2855249903739718031250,5188687661991616758000],[0,189897844693678509600,701137659710582910000],[47214898806038240160,6575726564328150961200,9059781299208688499400],[0,-8338490390389647600,556344247509737820000],[50841113951073862080,6402866946602361732000,6954997596353642707200],[0,-35678874156303470400,136903958847255600000],[27575843398796338128,2325060045579881423520,1832555111160060191520],[0,0,0],[5656548731550460128,-23828533408778978880,28407503683151651520]]
def witness_57 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_8, 4600, by norm_num, R7.Core.Certificates.Terminal014.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_9, 110400, by norm_num, R7.Core.Certificates.Terminal014.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_10, 1152, by norm_num, R7.Core.Certificates.Terminal014.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_11, 124416000, by norm_num, R7.Core.Certificates.Terminal014.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_12, 94058496000000, by norm_num, R7.Core.Certificates.Terminal014.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_13, 255989602713600000000, by norm_num, R7.Core.Certificates.Terminal014.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_14, 28554999594320249487360000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_14⟩
theorem bound_57 : minorBindings polynomial_57 witness_57 := by
 decide +kernel
theorem positive_57 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_57 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_57 ρ hρ u
def polynomial_58 : BiPoly := [[1422000625283752320,66759662962105159300,234052095785314408800],[0,42973459033570036000,110332237613690700000],[12882402591741799920,1082638937508555696300,2827548515785276567800],[0,226445535673861261200,557410184160011280000],[47542747213934542080,5929291759945994863500,10767547562520156037200],[0,253525593205554444000,997616525039379900000],[90797882319304308000,12821046717572831430000,17765657976709527345000],[0,-13854700111579267500,721257387273643500000],[93589870664260535040,11851337241724334256000,12894941928525490713600],[0,-42286073074137446400,162256543818969600000],[48400079121781183440,4080857602123980669600,3216431537286831309600],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_58 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_16, 46000, by norm_num, R7.Core.Certificates.Terminal014.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_17, 1840000, by norm_num, R7.Core.Certificates.Terminal014.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_18, 48000, by norm_num, R7.Core.Certificates.Terminal014.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_19, 2980800000000, by norm_num, R7.Core.Certificates.Terminal014.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_20, 42865200000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_21, 27776649600000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_22, 5164026257653401600000000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_22⟩
theorem bound_58 : minorBindings polynomial_58 witness_58 := by
 decide +kernel
theorem positive_58 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_58 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_58 ρ hρ u
def polynomial_59 : BiPoly := [[1994290934106637440,108288862485830566850,364988160523789269600],[0,36652519666067887000,118185982600784400000],[17250907694710387680,1573183081228947467700,4003923208276063816200],[0,178595326548810843600,539150258875947840000],[60499693657348333920,7799077874394745842750,14153525186650818427800],[0,181478587282922034000,861973447595109525000],[109386560306413299600,15634109257233168987000,21770295673709137689000],[0,-17321117618670106500,557250308142198300000],[106314809219488941120,13524730558672468968000,14736311901337166380800],[0,-29792460574960473600,114317110417910400000],[51653865953497565520,4355200970333996176800,3432662228869139296800],[0,0,0],[9427581219250766880,-39714222347964964800,47345839471919419200]]
def witness_59 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal014.polynomial_24, 23000, by norm_num, R7.Core.Certificates.Terminal014.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal014.polynomial_25, 920000, by norm_num, R7.Core.Certificates.Terminal014.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal014.polynomial_26, 48000, by norm_num, R7.Core.Certificates.Terminal014.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal014.polynomial_27, 25920000000, by norm_num, R7.Core.Certificates.Terminal014.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal014.polynomial_28, 2857680000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal014.polynomial_29, 1851776640000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal014.polynomial_30, 344268417176893440000000000000000, by norm_num, R7.Core.Certificates.Terminal014.positive_30⟩
theorem bound_59 : minorBindings polynomial_59 witness_59 := by
 decide +kernel
theorem positive_59 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_59 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_59 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry009
