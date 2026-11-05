import R7.Spectral.CertificateCore
import R7.Certificates.Spectral.Terminal.Terminal043
import R7.Certificates.Spectral.Terminal.Terminal044

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R7.Core.SpectralSliceCertificates.Entry029
open R7.Core.Univariate R7.Core.Bivariate R7.Core.SpectralCertificate R7.Core.MinorCertificates
def polynomial_174 : BiPoly := [[6049104598282089600,316808958025030441500,1044218021176259064000],[0,76628416312597480000,323364044648713500000],[64726256222320215600,5676548781002369884000,14589678271920830716500],[0,572901543433928935500,2070336665248874325000],[279953137081367467200,35479260930961181122500,64409688937103661423000],[0,824496116517376740000,4588298591410066500000],[620652443226095232000,88154079211590792390000,122444686631770855380000],[0,-163651814089633485000,4053467443592952000000],[734469379743022056000,93212113811380483500000,101488617892096979040000],[0,-295521987961301472000,1133951982371208000000],[431126755202420625600,36350496287827054704000,28650566634655808304000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
def witness_174 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_16, 6210000, by norm_num, R7.Core.Certificates.Terminal043.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_17, 46000000, by norm_num, R7.Core.Certificates.Terminal043.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_18, 2000000, by norm_num, R7.Core.Certificates.Terminal043.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_19, 3600000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_20, 8505000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_21, 771573600000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_22, 1434451738237056000000000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_22⟩
theorem bound_174 : minorBindings polynomial_174 witness_174 := by
 decide +kernel
theorem positive_174 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_174 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_174 ρ hρ u
def polynomial_175 : BiPoly := [[5559504885016773120,321979323736433276300,1048934783222949280800],[0,886557610368684000,211272655301448300000],[56008624350972398400,5256943913788925313500,13246507280074626418500],[0,120367418845157489400,1244954088048953610000],[227355510729967814880,29649386492213481178500,53794500533717098714200],[0,204037541032457277000,2535143307848533575000],[470552730393899358000,67543103032192295482500,94214823700056812595000],[0,-139684495537848145500,2062851795332524350000],[517089899447023432320,65890533137648248008000,71829407689295733388800],[0,-142715496625213881600,547615835389022400000],[280639114235537954400,23662115508113837496000,18649897148974063896000],[0,0,0],[56565487315504601280,-238285334087789788800,284075036831516515200]]
def witness_175 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal043.polynomial_24, 46000, by norm_num, R7.Core.Certificates.Terminal043.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal043.polynomial_25, 9200000, by norm_num, R7.Core.Certificates.Terminal043.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal043.polynomial_26, 2000000, by norm_num, R7.Core.Certificates.Terminal043.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal043.polynomial_27, 2700000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal043.polynomial_28, 85050000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal043.polynomial_29, 11573604000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal043.polynomial_30, 12910065644133504000000000000000000000, by norm_num, R7.Core.Certificates.Terminal043.positive_30⟩
theorem bound_175 : minorBindings polynomial_175 witness_175 := by
 decide +kernel
theorem positive_175 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_175 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_175 ρ hρ u
def polynomial_176 : BiPoly := [[154078160067699840,6049477713385667850,20249430683902635600],[0,6264294348047243000,15251250913784100000],[1793805296447358000,128078968742766793750,350785399658206657500],[0,49477723246698961800,113480596966231170000],[8556160248326822040,994596530315901603000,1808756409498178233600],[0,81647113041874746000,299488774513094100000],[21094630882878070800,2898057376221961176000,3970262047319086797000],[0,-4892228045887077000,319456482586781400000],[28044709050866291280,3511033408495326987000,3806815534159142635200],[0,-27389842786657209600,105097988610014400000],[18709274282369196960,1577474367207589166400,1243326476598270926400],[0,0,0],[4713790609625383440,-19857111173982482400,23672919735959709600]]
def witness_176 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_0, 69000, by norm_num, R7.Core.Certificates.Terminal044.positive_0⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_1, 11500000, by norm_num, R7.Core.Certificates.Terminal044.positive_1⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_2, 31250000, by norm_num, R7.Core.Certificates.Terminal044.positive_2⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_3, 5625000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_3⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_4, 354375000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_4⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_5, 3214890000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_5⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_6, 298844112132720000000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_6⟩
theorem bound_176 : minorBindings polynomial_176 witness_176 := by
 decide +kernel
theorem positive_176 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_176 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_176 ρ hρ u
def polynomial_177 : BiPoly := [[1040870350315774080,44951018148243694825,147976943295965467200],[0,35920375521012360000,71018890265007000000],[11986547421063491640,912051206714706499600,2444491078190892710100],[0,254806946709017966400,517635958663541160000],[56151520023791520720,6697417401571954179000,12174699250363091802300],[0,391946479691210829000,1327535021647097775000],[135827796168963070200,18851467220533761511500,25938959172321040893000],[0,-14055591065210887500,1358705103580440000000],[176859053836722915840,22239464966334177786000,24145866595217932185600],[0,-109198978478383348800,419009086168873200000],[115306070848949289960,9722043110942424536400,7662675132948039296400],[0,0,0],[28282743657752300640,-119142667043894894400,142037518415758257600]]
def witness_177 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_8, 11500, by norm_num, R7.Core.Certificates.Terminal044.positive_8⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_9, 460000, by norm_num, R7.Core.Certificates.Terminal044.positive_9⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_10, 16000, by norm_num, R7.Core.Certificates.Terminal044.positive_10⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_11, 4320000000, by norm_num, R7.Core.Certificates.Terminal044.positive_11⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_12, 136080000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_12⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_13, 24998984640000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_13⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_14, 13942870895664184320000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_14⟩
theorem bound_177 : minorBindings polynomial_177 witness_177 := by
 decide +kernel
theorem positive_177 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_177 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_177 ρ hρ u
def polynomial_178 : BiPoly := [[3254826769383794400,156323028470501493500,511441413674701746000],[0,79555959016060215000,131484596643220500000],[36330449314251709800,2978107550778673234500,7798783250902565007000],[0,500983646394463056000,912440242460381400000],[164848732709214216600,20286617376152249805000,36854365181982133869000],[0,704912056504678440000,2202933547856011500000],[385161527267521488000,54106119872586415710000,74821812052520505982500],[0,-7343740752477570000,2083097762616417750000],[482902622130442046400,61024468310010637110000,66356350455089743776000],[0,-151364920663105632000,580804673897448000000],[301992090318676711800,25462493861992064262000,20068911062482960062000],[0,0,0],[70706859144380751600,-297856667609737236000,355093796039395644000]]
def witness_178 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_16, 230000, by norm_num, R7.Core.Certificates.Terminal044.positive_16⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_17, 138000000, by norm_num, R7.Core.Certificates.Terminal044.positive_17⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_18, 18000000, by norm_num, R7.Core.Certificates.Terminal044.positive_18⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_19, 24300000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_19⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_20, 1653372000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_20⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_21, 506229438960000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_21⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_22, 705857839092999331200000000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_22⟩
theorem bound_178 : minorBindings polynomial_178 witness_178 := by
 decide +kernel
theorem positive_178 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_178 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_178 ρ hρ u
def polynomial_179 : BiPoly := [[5933099805953126400,315398480684377932875,1027218974127496626000],[0,71637135903095555000,102325882744341000000],[63630332840476099800,5605970976912875072000,14373328488022371357000],[0,397946089910852199000,662150079138821850000],[275808624976314486000,35006496909465421338750,63553215937901550615000],[0,501655344723805320000,1437812447575347000000],[613100256416928144000,87136217987670433305000,121068313335979896960000],[0,7945403177765970000,1201720392150358500000],[728018950060648209600,92419830590254598340000,100634725593408543264000],[0,-75682460331552816000,290402336948724000000],[429093138432597886800,36179031682695795012000,28515422452416865812000],[0,0,0],[94275812192507668800,-397142223479649648000,473458394719194192000]]
def witness_179 : Fin 7 → MinorWitness
 | 0 => ⟨R7.Core.Certificates.Terminal044.polynomial_24, 57500, by norm_num, R7.Core.Certificates.Terminal044.positive_24⟩
 | 1 => ⟨R7.Core.Certificates.Terminal044.polynomial_25, 23000000, by norm_num, R7.Core.Certificates.Terminal044.positive_25⟩
 | 2 => ⟨R7.Core.Certificates.Terminal044.polynomial_26, 8000000, by norm_num, R7.Core.Certificates.Terminal044.positive_26⟩
 | 3 => ⟨R7.Core.Certificates.Terminal044.polynomial_27, 21600000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_27⟩
 | 4 => ⟨R7.Core.Certificates.Terminal044.polynomial_28, 27216000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_28⟩
 | 5 => ⟨R7.Core.Certificates.Terminal044.polynomial_29, 14196954240000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_29⟩
 | 6 => ⟨R7.Core.Certificates.Terminal044.polynomial_30, 26393911983561830400000000000000000000000, by norm_num, R7.Core.Certificates.Terminal044.positive_30⟩
theorem bound_179 : minorBindings polynomial_179 witness_179 := by
 decide +kernel
theorem positive_179 (ρ u : ℝ) (hρ : 0 ≤ ρ) :
 0 < ∑ k ∈ Finset.range 13, evaluate (coefficient polynomial_179 k) ρ*u^k :=
 corrected_slice_pos _ _ bound_179 ρ hρ u
end R7.Core.SpectralSliceCertificates.Entry029
