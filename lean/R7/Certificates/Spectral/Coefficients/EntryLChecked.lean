import R7.Certificates.Spectral.Coefficients.EntryLData
import R7.Certificates.Spectral.Coefficients.EntryAChecked
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct60 : interpretKey p60 = e60.denote := by
  have he : powerKey p49 3=p60 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct49]
  rfl
theorem correct61 : interpretKey p61 = e61.denote := by
  have he : mulKey p55 p60=p61 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct55,correct60]
  rfl
theorem correct62 : interpretKey p62 = e62.denote := by
  have he : computeKey e62=p62 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e62
theorem correct63 : interpretKey p63 = e63.denote := by
  have he : mulKey p62 p7=p63 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct62,correct7]
  rfl
theorem correct64 : interpretKey p64 = e64.denote := by
  have he : mulKey p63 p49=p64 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct63,correct49]
  rfl
theorem correct65 : interpretKey p65 = e65.denote := by
  have he : computeKey e65=p65 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e65
theorem correct66 : interpretKey p66 = e66.denote := by
  have he : powerKey p49 2=p66 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct49]
  rfl
theorem correct67 : interpretKey p67 = e67.denote := by
  have he : mulKey p65 p66=p67 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct65,correct66]
  rfl
theorem correct68 : interpretKey p68 = e68.denote := by
  have he : addKey p64 p67=p68 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct64,correct67]
  rfl
theorem correct69 : interpretKey p69 = e69.denote := by
  have he : computeKey e69=p69 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e69
theorem correct70 : interpretKey p70 = e70.denote := by
  have he : computeKey e70=p70 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e70
theorem correct71 : interpretKey p71 = e71.denote := by
  have he : powerKey p6 4=p71 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct6]
  rfl
theorem correct72 : interpretKey p72 = e72.denote := by
  have he : mulKey p70 p71=p72 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct70,correct71]
  rfl
theorem correct73 : interpretKey p73 = e73.denote := by
  have he : computeKey e73=p73 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e73
theorem correct74 : interpretKey p74 = e74.denote := by
  have he : powerKey p26 4=p74 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct26]
  rfl
theorem correct75 : interpretKey p75 = e75.denote := by
  have he : powerKey p31 4=p75 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct31]
  rfl
theorem correct76 : interpretKey p76 = e76.denote := by
  have he : powerKey p36 4=p76 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct36]
  rfl
theorem correct77 : interpretKey p77 = e77.denote := by
  have he : powerKey p40 4=p77 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct40]
  rfl
theorem correct78 : interpretKey p78 = e78.denote := by
  have he : powerKey p43 4=p78 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct43]
  rfl
theorem correct79 : interpretKey p79 = e79.denote := by
  have he : addKey p77 p78=p79 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct77,correct78]
  rfl
theorem correct80 : interpretKey p80 = e80.denote := by
  have he : addKey p76 p79=p80 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct76,correct79]
  rfl
theorem correct81 : interpretKey p81 = e81.denote := by
  have he : addKey p75 p80=p81 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct75,correct80]
  rfl
theorem correct82 : interpretKey p82 = e82.denote := by
  have he : addKey p74 p81=p82 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct74,correct81]
  rfl
theorem correct83 : interpretKey p83 = e83.denote := by
  have he : addKey p71 p82=p83 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct71,correct82]
  rfl
theorem correct84 : interpretKey p84 = e84.denote := by
  have he : mulKey p73 p83=p84 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct73,correct83]
  rfl
theorem correct85 : interpretKey p85 = e85.denote := by
  have he : negKey p84=p85 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct84]
  rfl
theorem correct86 : interpretKey p86 = e86.denote := by
  have he : addKey p72 p85=p86 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct72,correct85]
  rfl
theorem correct87 : interpretKey p87 = e87.denote := by
  have he : mulKey p69 p86=p87 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct86]
  rfl
theorem correct88 : interpretKey p88 = e88.denote := by
  have he : addKey p68 p87=p88 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct68,correct87]
  rfl
theorem correct89 : interpretKey p89 = e89.denote := by
  have he : computeKey e89=p89 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e89
theorem correct90 : interpretKey p90 = e90.denote := by
  have he : powerKey p6 3=p90 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct6]
  rfl
theorem correct91 : interpretKey p91 = e91.denote := by
  have he : powerKey p26 3=p91 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct26]
  rfl
theorem correct92 : interpretKey p92 = e92.denote := by
  have he : powerKey p31 3=p92 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct31]
  rfl
theorem correct93 : interpretKey p93 = e93.denote := by
  have he : powerKey p36 3=p93 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct36]
  rfl
theorem correct94 : interpretKey p94 = e94.denote := by
  have he : powerKey p40 3=p94 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct40]
  rfl
theorem correct95 : interpretKey p95 = e95.denote := by
  have he : powerKey p43 3=p95 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct43]
  rfl
theorem correct96 : interpretKey p96 = e96.denote := by
  have he : addKey p94 p95=p96 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct94,correct95]
  rfl
theorem correct97 : interpretKey p97 = e97.denote := by
  have he : addKey p93 p96=p97 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct93,correct96]
  rfl
theorem correct98 : interpretKey p98 = e98.denote := by
  have he : addKey p92 p97=p98 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct92,correct97]
  rfl
theorem correct99 : interpretKey p99 = e99.denote := by
  have he : addKey p91 p98=p99 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct91,correct98]
  rfl
theorem correct100 : interpretKey p100 = e100.denote := by
  have he : addKey p90 p99=p100 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct90,correct99]
  rfl
theorem correct101 : interpretKey p101 = e101.denote := by
  have he : mulKey p89 p100=p101 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct89,correct100]
  rfl
theorem correct102 : interpretKey p102 = e102.denote := by
  have he : mulKey p101 p6=p102 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct101,correct6]
  rfl
theorem correct103 : interpretKey p103 = e103.denote := by
  have he : addKey p88 p102=p103 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct88,correct102]
  rfl
theorem correct104 : interpretKey p104 = e104.denote := by
  have he : computeKey e104=p104 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e104
theorem correct105 : interpretKey p105 = e105.denote := by
  have he : mulKey p104 p83=p105 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct104,correct83]
  rfl
theorem correct106 : interpretKey p106 = e106.denote := by
  have he : addKey p103 p105=p106 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct103,correct105]
  rfl
theorem correct107 : interpretKey p107 = e107.denote := by
  have he : mulKey p61 p106=p107 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct61,correct106]
  rfl
theorem correct108 : interpretKey p108 = e108.denote := by
  have he : computeKey e108=p108 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e108
theorem correct109 : interpretKey p109 = e109.denote := by
  have he : computeKey e109=p109 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e109
theorem correct110 : interpretKey p110 = e110.denote := by
  have he : mulKey p109 p90=p110 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct109,correct90]
  rfl
theorem correct111 : interpretKey p111 = e111.denote := by
  have he : mulKey p110 p49=p111 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct110,correct49]
  rfl
theorem correct112 : interpretKey p112 = e112.denote := by
  have he : computeKey e112=p112 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e112
theorem correct113 : interpretKey p113 = e113.denote := by
  have he : mulKey p112 p6=p113 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct112,correct6]
  rfl
theorem correct114 : interpretKey p114 = e114.denote := by
  have he : mulKey p113 p7=p114 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct113,correct7]
  rfl
theorem correct115 : interpretKey p115 = e115.denote := by
  have he : mulKey p114 p49=p115 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct114,correct49]
  rfl
theorem correct116 : interpretKey p116 = e116.denote := by
  have he : addKey p111 p115=p116 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct111,correct115]
  rfl
theorem correct117 : interpretKey p117 = e117.denote := by
  have he : computeKey e117=p117 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e117
theorem correct118 : interpretKey p118 = e118.denote := by
  have he : mulKey p117 p66=p118 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct117,correct66]
  rfl
theorem correct119 : interpretKey p119 = e119.denote := by
  have he : mulKey p7 p49=p119 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct7,correct49]
  rfl
theorem correct120 : interpretKey p120 = e120.denote := by
  have he : mulKey p19 p71=p120 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct19,correct71]
  rfl
theorem correct121 : interpretKey p121 = e121.denote := by
  have he : negKey p120=p121 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct120]
  rfl
theorem correct122 : interpretKey p122 = e122.denote := by
  have he : addKey p119 p121=p122 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct119,correct121]
  rfl
theorem correct123 : interpretKey p123 = e123.denote := by
  have he : mulKey p69 p122=p123 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct122]
  rfl
theorem correct124 : interpretKey p124 = e124.denote := by
  have he : addKey p118 p123=p124 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct118,correct123]
  rfl
theorem correct125 : interpretKey p125 = e125.denote := by
  have he : computeKey e125=p125 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e125
theorem correct126 : interpretKey p126 = e126.denote := by
  have he : mulKey p125 p100=p126 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct125,correct100]
  rfl
theorem correct127 : interpretKey p127 = e127.denote := by
  have he : mulKey p126 p6=p127 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct126,correct6]
  rfl
theorem correct128 : interpretKey p128 = e128.denote := by
  have he : negKey p127=p128 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct127]
  rfl
theorem correct129 : interpretKey p129 = e129.denote := by
  have he : addKey p124 p128=p129 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct124,correct128]
  rfl
theorem correct130 : interpretKey p130 = e130.denote := by
  have he : computeKey e130=p130 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e130
theorem correct131 : interpretKey p131 = e131.denote := by
  have he : mulKey p130 p83=p131 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct130,correct83]
  rfl
theorem correct132 : interpretKey p132 = e132.denote := by
  have he : negKey p131=p132 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct131]
  rfl
theorem correct133 : interpretKey p133 = e133.denote := by
  have he : addKey p129 p132=p133 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct129,correct132]
  rfl
theorem correct134 : interpretKey p134 = e134.denote := by
  have he : mulKey p133 p6=p134 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct6]
  rfl
theorem correct135 : interpretKey p135 = e135.denote := by
  have he : addKey p116 p134=p135 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct116,correct134]
  rfl
theorem correct136 : interpretKey p136 = e136.denote := by
  have he : mulKey p108 p135=p136 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct108,correct135]
  rfl
theorem correct137 : interpretKey p137 = e137.denote := by
  have he : mulKey p136 p135=p137 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct136,correct135]
  rfl
theorem correct138 : interpretKey p138 = e138.denote := by
  have he : computeKey e138=p138 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e138
theorem correct139 : interpretKey p139 = e139.denote := by
  have he : mulKey p109 p91=p139 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct109,correct91]
  rfl
theorem correct140 : interpretKey p140 = e140.denote := by
  have he : mulKey p139 p49=p140 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct139,correct49]
  rfl
theorem correct141 : interpretKey p141 = e141.denote := by
  have he : mulKey p113 p27=p141 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct113,correct27]
  rfl
theorem correct142 : interpretKey p142 = e142.denote := by
  have he : mulKey p141 p49=p142 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct141,correct49]
  rfl
theorem correct143 : interpretKey p143 = e143.denote := by
  have he : addKey p140 p142=p143 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct140,correct142]
  rfl
theorem correct144 : interpretKey p144 = e144.denote := by
  have he : mulKey p133 p26=p144 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct26]
  rfl
theorem correct145 : interpretKey p145 = e145.denote := by
  have he : addKey p143 p144=p145 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct143,correct144]
  rfl
theorem correct146 : interpretKey p146 = e146.denote := by
  have he : mulKey p138 p145=p146 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct145]
  rfl
theorem correct147 : interpretKey p147 = e147.denote := by
  have he : mulKey p146 p145=p147 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct146,correct145]
  rfl
theorem correct148 : interpretKey p148 = e148.denote := by
  have he : mulKey p109 p92=p148 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct109,correct92]
  rfl
theorem correct149 : interpretKey p149 = e149.denote := by
  have he : mulKey p148 p49=p149 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct148,correct49]
  rfl
theorem correct150 : interpretKey p150 = e150.denote := by
  have he : mulKey p113 p32=p150 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct113,correct32]
  rfl
theorem correct151 : interpretKey p151 = e151.denote := by
  have he : mulKey p150 p49=p151 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct150,correct49]
  rfl
theorem correct152 : interpretKey p152 = e152.denote := by
  have he : addKey p149 p151=p152 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct149,correct151]
  rfl
theorem correct153 : interpretKey p153 = e153.denote := by
  have he : mulKey p133 p31=p153 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct31]
  rfl
theorem correct154 : interpretKey p154 = e154.denote := by
  have he : addKey p152 p153=p154 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct152,correct153]
  rfl
theorem correct155 : interpretKey p155 = e155.denote := by
  have he : mulKey p138 p154=p155 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct154]
  rfl
theorem correct156 : interpretKey p156 = e156.denote := by
  have he : mulKey p155 p154=p156 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct155,correct154]
  rfl
theorem correct157 : interpretKey p157 = e157.denote := by
  have he : mulKey p109 p93=p157 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct109,correct93]
  rfl
theorem correct158 : interpretKey p158 = e158.denote := by
  have he : mulKey p157 p49=p158 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct157,correct49]
  rfl
theorem correct159 : interpretKey p159 = e159.denote := by
  have he : mulKey p113 p37=p159 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct113,correct37]
  rfl
theorem correct160 : interpretKey p160 = e160.denote := by
  have he : mulKey p159 p49=p160 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct159,correct49]
  rfl
theorem correct161 : interpretKey p161 = e161.denote := by
  have he : addKey p158 p160=p161 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct158,correct160]
  rfl
theorem correct162 : interpretKey p162 = e162.denote := by
  have he : mulKey p133 p36=p162 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct36]
  rfl
theorem correct163 : interpretKey p163 = e163.denote := by
  have he : addKey p161 p162=p163 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct161,correct162]
  rfl
theorem correct164 : interpretKey p164 = e164.denote := by
  have he : mulKey p138 p163=p164 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct163]
  rfl
theorem correct165 : interpretKey p165 = e165.denote := by
  have he : mulKey p164 p163=p165 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct164,correct163]
  rfl
theorem correct166 : interpretKey p166 = e166.denote := by
  have he : mulKey p109 p94=p166 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct109,correct94]
  rfl
theorem correct167 : interpretKey p167 = e167.denote := by
  have he : mulKey p166 p49=p167 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct166,correct49]
  rfl
theorem correct168 : interpretKey p168 = e168.denote := by
  have he : mulKey p113 p41=p168 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct113,correct41]
  rfl
theorem correct169 : interpretKey p169 = e169.denote := by
  have he : mulKey p168 p49=p169 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct168,correct49]
  rfl
theorem correct170 : interpretKey p170 = e170.denote := by
  have he : addKey p167 p169=p170 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct167,correct169]
  rfl
theorem correct171 : interpretKey p171 = e171.denote := by
  have he : mulKey p133 p40=p171 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct40]
  rfl
theorem correct172 : interpretKey p172 = e172.denote := by
  have he : addKey p170 p171=p172 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct170,correct171]
  rfl
theorem correct173 : interpretKey p173 = e173.denote := by
  have he : mulKey p138 p172=p173 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct172]
  rfl
theorem correct174 : interpretKey p174 = e174.denote := by
  have he : mulKey p173 p172=p174 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct173,correct172]
  rfl
theorem correct175 : interpretKey p175 = e175.denote := by
  have he : mulKey p109 p95=p175 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct109,correct95]
  rfl
theorem correct176 : interpretKey p176 = e176.denote := by
  have he : mulKey p175 p49=p176 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct175,correct49]
  rfl
theorem correct177 : interpretKey p177 = e177.denote := by
  have he : mulKey p113 p44=p177 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct113,correct44]
  rfl
theorem correct178 : interpretKey p178 = e178.denote := by
  have he : mulKey p177 p49=p178 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct177,correct49]
  rfl
theorem correct179 : interpretKey p179 = e179.denote := by
  have he : addKey p176 p178=p179 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct176,correct178]
  rfl
theorem correct180 : interpretKey p180 = e180.denote := by
  have he : mulKey p133 p43=p180 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct43]
  rfl
theorem correct181 : interpretKey p181 = e181.denote := by
  have he : addKey p179 p180=p181 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct179,correct180]
  rfl
theorem correct182 : interpretKey p182 = e182.denote := by
  have he : mulKey p138 p181=p182 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct181]
  rfl
theorem correct183 : interpretKey p183 = e183.denote := by
  have he : mulKey p182 p181=p183 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct182,correct181]
  rfl
theorem correct184 : interpretKey p184 = e184.denote := by
  have he : addKey p174 p183=p184 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct174,correct183]
  rfl
theorem correct185 : interpretKey p185 = e185.denote := by
  have he : addKey p165 p184=p185 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct165,correct184]
  rfl
theorem correct186 : interpretKey p186 = e186.denote := by
  have he : addKey p156 p185=p186 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct156,correct185]
  rfl
theorem correct187 : interpretKey p187 = e187.denote := by
  have he : addKey p147 p186=p187 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct147,correct186]
  rfl
theorem correct188 : interpretKey p188 = e188.denote := by
  have he : addKey p137 p187=p188 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct137,correct187]
  rfl
theorem correct189 : interpretKey p189 = e189.denote := by
  have he : computeKey e189=p189 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e189
theorem correct190 : interpretKey p190 = e190.denote := by
  have he : addKey p173 p182=p190 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct173,correct182]
  rfl
theorem correct191 : interpretKey p191 = e191.denote := by
  have he : addKey p164 p190=p191 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct164,correct190]
  rfl
theorem correct192 : interpretKey p192 = e192.denote := by
  have he : addKey p155 p191=p192 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct155,correct191]
  rfl
theorem correct193 : interpretKey p193 = e193.denote := by
  have he : addKey p146 p192=p193 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct146,correct192]
  rfl
theorem correct194 : interpretKey p194 = e194.denote := by
  have he : addKey p136 p193=p194 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct136,correct193]
  rfl
theorem correct195 : interpretKey p195 = e195.denote := by
  have he : mulKey p189 p194=p195 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct189,correct194]
  rfl
theorem correct196 : interpretKey p196 = e196.denote := by
  have he : mulKey p195 p194=p196 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct195,correct194]
  rfl
theorem correct197 : interpretKey p197 = e197.denote := by
  have he : negKey p196=p197 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct196]
  rfl
theorem correct198 : interpretKey p198 = e198.denote := by
  have he : addKey p188 p197=p198 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct188,correct197]
  rfl
theorem correct199 : interpretKey p199 = e199.denote := by
  have he : mulKey p54 p198=p199 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct54,correct198]
  rfl
theorem correct200 : interpretKey p200 = e200.denote := by
  have he : negKey p199=p200 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct199]
  rfl
theorem correct201 : interpretKey p201 = e201.denote := by
  have he : addKey p107 p200=p201 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct107,correct200]
  rfl
theorem correct202 : interpretKey p202 = e202.denote := by
  have he : computeKey e202=p202 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e202
theorem correct203 : interpretKey p203 = e203.denote := by
  have he : mulKey p136 p6=p203 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct136,correct6]
  rfl
theorem correct204 : interpretKey p204 = e204.denote := by
  have he : mulKey p146 p26=p204 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct146,correct26]
  rfl
theorem correct205 : interpretKey p205 = e205.denote := by
  have he : mulKey p155 p31=p205 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct155,correct31]
  rfl
theorem correct206 : interpretKey p206 = e206.denote := by
  have he : mulKey p164 p36=p206 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct164,correct36]
  rfl
theorem correct207 : interpretKey p207 = e207.denote := by
  have he : mulKey p173 p40=p207 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct173,correct40]
  rfl
theorem correct208 : interpretKey p208 = e208.denote := by
  have he : mulKey p182 p43=p208 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct182,correct43]
  rfl
theorem correct209 : interpretKey p209 = e209.denote := by
  have he : addKey p207 p208=p209 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct207,correct208]
  rfl
theorem correct210 : interpretKey p210 = e210.denote := by
  have he : addKey p206 p209=p210 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct206,correct209]
  rfl
theorem correct211 : interpretKey p211 = e211.denote := by
  have he : addKey p205 p210=p211 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct205,correct210]
  rfl
theorem correct212 : interpretKey p212 = e212.denote := by
  have he : addKey p204 p211=p212 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct204,correct211]
  rfl
theorem correct213 : interpretKey p213 = e213.denote := by
  have he : addKey p203 p212=p213 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct203,correct212]
  rfl
theorem correct214 : interpretKey p214 = e214.denote := by
  have he : mulKey p108 p6=p214 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct108,correct6]
  rfl
theorem correct215 : interpretKey p215 = e215.denote := by
  have he : mulKey p138 p26=p215 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct26]
  rfl
theorem correct216 : interpretKey p216 = e216.denote := by
  have he : mulKey p138 p31=p216 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct31]
  rfl
theorem correct217 : interpretKey p217 = e217.denote := by
  have he : mulKey p138 p36=p217 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct36]
  rfl
theorem correct218 : interpretKey p218 = e218.denote := by
  have he : mulKey p138 p40=p218 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct40]
  rfl
theorem correct219 : interpretKey p219 = e219.denote := by
  have he : mulKey p138 p43=p219 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct43]
  rfl
theorem correct220 : interpretKey p220 = e220.denote := by
  have he : addKey p218 p219=p220 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct218,correct219]
  rfl
theorem correct221 : interpretKey p221 = e221.denote := by
  have he : addKey p217 p220=p221 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct217,correct220]
  rfl
theorem correct222 : interpretKey p222 = e222.denote := by
  have he : addKey p216 p221=p222 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct216,correct221]
  rfl
theorem correct223 : interpretKey p223 = e223.denote := by
  have he : addKey p215 p222=p223 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct215,correct222]
  rfl
theorem correct224 : interpretKey p224 = e224.denote := by
  have he : addKey p214 p223=p224 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct214,correct223]
  rfl
theorem correct225 : interpretKey p225 = e225.denote := by
  have he : mulKey p195 p224=p225 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct195,correct224]
  rfl
theorem correct226 : interpretKey p226 = e226.denote := by
  have he : negKey p225=p226 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct225]
  rfl
theorem correct227 : interpretKey p227 = e227.denote := by
  have he : addKey p213 p226=p227 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct213,correct226]
  rfl
theorem correct228 : interpretKey p228 = e228.denote := by
  have he : powerKey p227 2=p228 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct227]
  rfl
theorem correct229 : interpretKey p229 = e229.denote := by
  have he : mulKey p202 p228=p229 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct202,correct228]
  rfl
theorem correct230 : interpretKey p230 = e230.denote := by
  have he : negKey p229=p230 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct229]
  rfl
theorem correct231 : interpretKey p231 = e231.denote := by
  have he : addKey p201 p230=p231 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct201,correct230]
  rfl
theorem correct232 : interpretKey p232 = e232.denote := by
  have he : computeKey e232=p232 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e232
theorem correct233 : interpretKey p233 = e233.denote := by
  have he : mulKey p232 p57=p233 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct232,correct57]
  rfl
theorem correct234 : interpretKey p234 = e234.denote := by
  have he : negKey p233=p234 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct233]
  rfl
theorem correct235 : interpretKey p235 = e235.denote := by
  have he : addKey p231 p234=p235 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct231,correct234]
  rfl
theorem correct236 : interpretKey p236 = e236.denote := by
  have he : mulKey p0 p235=p236 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct0,correct235]
  rfl
theorem entryL_raw : interpretKey p236 = e236.denote := correct236
end R7.Core.SpectralCoefficient.Expansion
