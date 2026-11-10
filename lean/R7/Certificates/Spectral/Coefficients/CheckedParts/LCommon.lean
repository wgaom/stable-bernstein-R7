import R7.Certificates.Spectral.Coefficients.CheckedParts.ACommon
import R7.Certificates.Spectral.Coefficients.DataParts.EntryLData
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
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
  have he : squareKey p49=p66 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct49]
  rfl
theorem correct67 : interpretKey p67 = e67.denote := by
  have he : mulKey p65 p66=p67 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct65,correct66]
  rfl
theorem correct68 : interpretKey p68 = e68.denote := by
  have he : interpretKey p68 = interpretKey p64 + interpretKey p67 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct64,correct67]
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
  have he : interpretKey p79 = interpretKey p77 + interpretKey p78 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct77,correct78]
  rfl
theorem correct80 : interpretKey p80 = e80.denote := by
  have he : interpretKey p80 = interpretKey p76 + interpretKey p79 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct76,correct79]
  rfl
theorem correct81 : interpretKey p81 = e81.denote := by
  have he : interpretKey p81 = interpretKey p75 + interpretKey p80 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct75,correct80]
  rfl
theorem correct82 : interpretKey p82 = e82.denote := by
  have he : interpretKey p82 = interpretKey p74 + interpretKey p81 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct74,correct81]
  rfl
theorem correct83 : interpretKey p83 = e83.denote := by
  have he : interpretKey p83 = interpretKey p71 + interpretKey p82 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct71,correct82]
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
  have he : interpretKey p86 = interpretKey p72 + interpretKey p85 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct72,correct85]
  rfl
theorem correct87 : interpretKey p87 = e87.denote := by
  have he : mulKey p69 p86=p87 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct86]
  rfl
theorem correct88 : interpretKey p88 = e88.denote := by
  have he : interpretKey p88 = interpretKey p68 + interpretKey p87 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct68,correct87]
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
  have he : interpretKey p96 = interpretKey p94 + interpretKey p95 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct94,correct95]
  rfl
theorem correct97 : interpretKey p97 = e97.denote := by
  have he : interpretKey p97 = interpretKey p93 + interpretKey p96 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct93,correct96]
  rfl
theorem correct98 : interpretKey p98 = e98.denote := by
  have he : interpretKey p98 = interpretKey p92 + interpretKey p97 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct92,correct97]
  rfl
theorem correct99 : interpretKey p99 = e99.denote := by
  have he : interpretKey p99 = interpretKey p91 + interpretKey p98 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct91,correct98]
  rfl
theorem correct100 : interpretKey p100 = e100.denote := by
  have he : interpretKey p100 = interpretKey p90 + interpretKey p99 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct90,correct99]
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
  have he : interpretKey p103 = interpretKey p88 + interpretKey p102 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct88,correct102]
  rfl
theorem correct104 : interpretKey p104 = e104.denote := by
  have he : computeKey e104=p104 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e104
theorem correct105 : interpretKey p105 = e105.denote := by
  have he : mulKey p104 p83=p105 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct104,correct83]
  rfl
theorem correct106 : interpretKey p106 = e106.denote := by
  have he : interpretKey p106 = interpretKey p103 + interpretKey p105 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct103,correct105]
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
  have he : interpretKey p116 = interpretKey p111 + interpretKey p115 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct111,correct115]
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
  have he : interpretKey p122 = interpretKey p119 + interpretKey p121 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct119,correct121]
  rfl
theorem correct123 : interpretKey p123 = e123.denote := by
  have he : mulKey p69 p122=p123 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct122]
  rfl
theorem correct124 : interpretKey p124 = e124.denote := by
  have he : interpretKey p124 = interpretKey p118 + interpretKey p123 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct118,correct123]
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
  have he : interpretKey p129 = interpretKey p124 + interpretKey p128 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct124,correct128]
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
  have he : interpretKey p133 = interpretKey p129 + interpretKey p132 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct129,correct132]
  rfl
theorem correct134 : interpretKey p134 = e134.denote := by
  have he : mulKey p133 p6=p134 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct6]
  rfl
theorem correct135 : interpretKey p135 = e135.denote := by
  have he : interpretKey p135 = interpretKey p116 + interpretKey p134 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct116,correct134]
  rfl
theorem correct136 : interpretKey p136 = e136.denote := by
  have he : mulKey p108 p135=p136 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct108,correct135]
  rfl
theorem correct138 : interpretKey p138 = e138.denote := by
  have he : computeKey e138=p138 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e138
end R7.Core.SpectralCoefficient.Expansion
