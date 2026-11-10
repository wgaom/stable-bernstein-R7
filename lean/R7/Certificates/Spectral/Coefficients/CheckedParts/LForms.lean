import R7.Certificates.Spectral.Coefficients.CheckedParts.LCommon
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
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
  have he : interpretKey p143 = interpretKey p140 + interpretKey p142 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct140,correct142]
  rfl
theorem correct144 : interpretKey p144 = e144.denote := by
  have he : mulKey p133 p26=p144 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct26]
  rfl
theorem correct145 : interpretKey p145 = e145.denote := by
  have he : interpretKey p145 = interpretKey p143 + interpretKey p144 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct143,correct144]
  rfl
theorem correct146 : interpretKey p146 = e146.denote := by
  have he : mulKey p138 p145=p146 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct145]
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
  have he : interpretKey p152 = interpretKey p149 + interpretKey p151 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct149,correct151]
  rfl
theorem correct153 : interpretKey p153 = e153.denote := by
  have he : mulKey p133 p31=p153 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct31]
  rfl
theorem correct154 : interpretKey p154 = e154.denote := by
  have he : interpretKey p154 = interpretKey p152 + interpretKey p153 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct152,correct153]
  rfl
theorem correct155 : interpretKey p155 = e155.denote := by
  have he : mulKey p138 p154=p155 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct154]
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
  have he : interpretKey p161 = interpretKey p158 + interpretKey p160 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct158,correct160]
  rfl
theorem correct162 : interpretKey p162 = e162.denote := by
  have he : mulKey p133 p36=p162 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct36]
  rfl
theorem correct163 : interpretKey p163 = e163.denote := by
  have he : interpretKey p163 = interpretKey p161 + interpretKey p162 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct161,correct162]
  rfl
theorem correct164 : interpretKey p164 = e164.denote := by
  have he : mulKey p138 p163=p164 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct163]
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
  have he : interpretKey p170 = interpretKey p167 + interpretKey p169 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct167,correct169]
  rfl
theorem correct171 : interpretKey p171 = e171.denote := by
  have he : mulKey p133 p40=p171 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct40]
  rfl
theorem correct172 : interpretKey p172 = e172.denote := by
  have he : interpretKey p172 = interpretKey p170 + interpretKey p171 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct170,correct171]
  rfl
theorem correct173 : interpretKey p173 = e173.denote := by
  have he : mulKey p138 p172=p173 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct172]
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
  have he : interpretKey p179 = interpretKey p176 + interpretKey p178 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct176,correct178]
  rfl
theorem correct180 : interpretKey p180 = e180.denote := by
  have he : mulKey p133 p43=p180 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct133,correct43]
  rfl
theorem correct181 : interpretKey p181 = e181.denote := by
  have he : interpretKey p181 = interpretKey p179 + interpretKey p180 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct179,correct180]
  rfl
theorem correct182 : interpretKey p182 = e182.denote := by
  have he : mulKey p138 p181=p182 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct138,correct181]
  rfl
end R7.Core.SpectralCoefficient.Expansion
