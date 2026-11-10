import R7.Certificates.Spectral.Coefficients.DataParts.EntryAData
import R7.Spectral.RationalCrossArithmetic
set_option Elab.async false
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct0 : interpretKey p0 = e0.denote := by
  have he : computeKey e0=p0 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e0
theorem correct1 : interpretKey p1 = e1.denote := by
  have he : computeKey e1=p1 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e1
theorem correct2 : interpretKey p2 = e2.denote := by
  have he : computeKey e2=p2 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e2
theorem correct3 : interpretKey p3 = e3.denote := by
  have he : computeKey e3=p3 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e3
theorem correct4 : interpretKey p4 = e4.denote := by
  have he : computeKey e4=p4 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e4
theorem correct5 : interpretKey p5 = e5.denote := by
  have he : computeKey e5=p5 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e5
theorem correct6 : interpretKey p6 = e6.denote := by
  have he : mulKey p4 p5=p6 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct4,correct5]
  rfl
theorem correct7 : interpretKey p7 = e7.denote := by
  have he : squareKey p6=p7 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct6]
  rfl
theorem correct8 : interpretKey p8 = e8.denote := by
  have he : negKey p5=p8 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct5]
  rfl
theorem correct9 : interpretKey p9 = e9.denote := by
  have he : computeKey e9=p9 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e9
theorem correct10 : interpretKey p10 = e10.denote := by
  have he : computeKey e10=p10 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e10
theorem correct11 : interpretKey p11 = e11.denote := by
  have he : mulKey p9 p10=p11 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct9,correct10]
  rfl
theorem correct12 : interpretKey p12 = e12.denote := by
  have he : negKey p11=p12 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct11]
  rfl
theorem correct13 : interpretKey p13 = e13.denote := by
  have he : interpretKey p13 = interpretKey p8 + interpretKey p12 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct8,correct12]
  rfl
theorem correct14 : interpretKey p14 = e14.denote := by
  have he : computeKey e14=p14 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e14
theorem correct15 : interpretKey p15 = e15.denote := by
  have he : computeKey e15=p15 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e15
theorem correct16 : interpretKey p16 = e16.denote := by
  have he : mulKey p14 p15=p16 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct14,correct15]
  rfl
theorem correct17 : interpretKey p17 = e17.denote := by
  have he : negKey p16=p17 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct16]
  rfl
theorem correct18 : interpretKey p18 = e18.denote := by
  have he : interpretKey p18 = interpretKey p13 + interpretKey p17 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct13,correct17]
  rfl
theorem correct19 : interpretKey p19 = e19.denote := by
  have he : computeKey e19=p19 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e19
theorem correct20 : interpretKey p20 = e20.denote := by
  have he : computeKey e20=p20 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e20
theorem correct21 : interpretKey p21 = e21.denote := by
  have he : mulKey p19 p20=p21 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct19,correct20]
  rfl
theorem correct22 : interpretKey p22 = e22.denote := by
  have he : negKey p21=p22 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct21]
  rfl
theorem correct23 : interpretKey p23 = e23.denote := by
  have he : interpretKey p23 = interpretKey p18 + interpretKey p22 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct18,correct22]
  rfl
theorem correct24 : interpretKey p24 = e24.denote := by
  have he : computeKey e24=p24 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e24
theorem correct25 : interpretKey p25 = e25.denote := by
  have he : negKey p24=p25 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct24]
  rfl
theorem correct26 : interpretKey p26 = e26.denote := by
  have he : interpretKey p26 = interpretKey p23 + interpretKey p25 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct23,correct25]
  rfl
theorem correct27 : interpretKey p27 = e27.denote := by
  have he : squareKey p26=p27 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct26]
  rfl
theorem correct28 : interpretKey p28 = e28.denote := by
  have he : interpretKey p28 = interpretKey p8 + interpretKey p10 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct8,correct10]
  rfl
theorem correct29 : interpretKey p29 = e29.denote := by
  have he : interpretKey p29 = interpretKey p28 + interpretKey p17 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct28,correct17]
  rfl
theorem correct30 : interpretKey p30 = e30.denote := by
  have he : interpretKey p30 = interpretKey p29 + interpretKey p22 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct29,correct22]
  rfl
theorem correct31 : interpretKey p31 = e31.denote := by
  have he : interpretKey p31 = interpretKey p30 + interpretKey p25 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct30,correct25]
  rfl
theorem correct32 : interpretKey p32 = e32.denote := by
  have he : squareKey p31=p32 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct31]
  rfl
theorem correct33 : interpretKey p33 = e33.denote := by
  have he : mulKey p19 p15=p33 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct19,correct15]
  rfl
theorem correct34 : interpretKey p34 = e34.denote := by
  have he : interpretKey p34 = interpretKey p28 + interpretKey p33 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct28,correct33]
  rfl
theorem correct35 : interpretKey p35 = e35.denote := by
  have he : interpretKey p35 = interpretKey p34 + interpretKey p22 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct34,correct22]
  rfl
theorem correct36 : interpretKey p36 = e36.denote := by
  have he : interpretKey p36 = interpretKey p35 + interpretKey p25 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct35,correct25]
  rfl
theorem correct37 : interpretKey p37 = e37.denote := by
  have he : squareKey p36=p37 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct36]
  rfl
theorem correct38 : interpretKey p38 = e38.denote := by
  have he : mulKey p14 p20=p38 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct14,correct20]
  rfl
theorem correct39 : interpretKey p39 = e39.denote := by
  have he : interpretKey p39 = interpretKey p34 + interpretKey p38 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct34,correct38]
  rfl
theorem correct40 : interpretKey p40 = e40.denote := by
  have he : interpretKey p40 = interpretKey p39 + interpretKey p25 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct39,correct25]
  rfl
theorem correct41 : interpretKey p41 = e41.denote := by
  have he : squareKey p40=p41 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct40]
  rfl
theorem correct42 : interpretKey p42 = e42.denote := by
  have he : mulKey p9 p24=p42 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct9,correct24]
  rfl
theorem correct43 : interpretKey p43 = e43.denote := by
  have he : interpretKey p43 = interpretKey p39 + interpretKey p42 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct39,correct42]
  rfl
theorem correct44 : interpretKey p44 = e44.denote := by
  have he : squareKey p43=p44 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_square,correct43]
  rfl
theorem correct45 : interpretKey p45 = e45.denote := by
  have he : interpretKey p45 = interpretKey p41 + interpretKey p44 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct41,correct44]
  rfl
theorem correct46 : interpretKey p46 = e46.denote := by
  have he : interpretKey p46 = interpretKey p37 + interpretKey p45 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct37,correct45]
  rfl
theorem correct47 : interpretKey p47 = e47.denote := by
  have he : interpretKey p47 = interpretKey p32 + interpretKey p46 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct32,correct46]
  rfl
theorem correct48 : interpretKey p48 = e48.denote := by
  have he : interpretKey p48 = interpretKey p27 + interpretKey p47 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct27,correct47]
  rfl
theorem correct49 : interpretKey p49 = e49.denote := by
  have he : interpretKey p49 = interpretKey p7 + interpretKey p48 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct7,correct48]
  rfl
theorem correct50 : interpretKey p50 = e50.denote := by
  have he : mulKey p3 p49=p50 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct3,correct49]
  rfl
theorem correct51 : interpretKey p51 = e51.denote := by
  have he : computeKey e51=p51 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e51
theorem correct52 : interpretKey p52 = e52.denote := by
  have he : mulKey p51 p7=p52 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct51,correct7]
  rfl
theorem correct53 : interpretKey p53 = e53.denote := by
  have he : negKey p52=p53 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct52]
  rfl
theorem correct54 : interpretKey p54 = e54.denote := by
  have he : interpretKey p54 = interpretKey p50 + interpretKey p53 :=
    RationalCrossAdd.verifyAdd_sound _ _ _ (by decide +kernel)
  rw [he,correct50,correct53]
  rfl
theorem correct55 : interpretKey p55 = e55.denote := by
  have he : mulKey p2 p54=p55 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct2,correct54]
  rfl

end R7.Core.SpectralCoefficient.Expansion
