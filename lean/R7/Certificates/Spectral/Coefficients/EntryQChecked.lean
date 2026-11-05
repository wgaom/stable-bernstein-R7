import R7.Certificates.Spectral.Coefficients.EntryQData
import R7.Certificates.Spectral.Coefficients.EntryLChecked
namespace R7.Core.SpectralCoefficient.Expansion
open R7.ComputablePolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem correct237 : interpretKey p237 = e237.denote := by
  have he : mulKey p55 p49=p237 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct55,correct49]
  rfl
theorem correct238 : interpretKey p238 = e238.denote := by
  have he : computeKey e238=p238 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e238
theorem correct239 : interpretKey p239 = e239.denote := by
  have he : powerKey p49 4=p239 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct49]
  rfl
theorem correct240 : interpretKey p240 = e240.denote := by
  have he : mulKey p238 p239=p240 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct238,correct239]
  rfl
theorem correct241 : interpretKey p241 = e241.denote := by
  have he : computeKey e241=p241 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e241
theorem correct242 : interpretKey p242 = e242.denote := by
  have he : computeKey e242=p242 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e242
theorem correct243 : interpretKey p243 = e243.denote := by
  have he : mulKey p242 p7=p243 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct7]
  rfl
theorem correct244 : interpretKey p244 = e244.denote := by
  have he : mulKey p243 p49=p244 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct243,correct49]
  rfl
theorem correct245 : interpretKey p245 = e245.denote := by
  have he : mulKey p69 p71=p245 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct71]
  rfl
theorem correct246 : interpretKey p246 = e246.denote := by
  have he : addKey p244 p245=p246 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct244,correct245]
  rfl
theorem correct247 : interpretKey p247 = e247.denote := by
  have he : computeKey e247=p247 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e247
theorem correct248 : interpretKey p248 = e248.denote := by
  have he : mulKey p247 p100=p248 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct247,correct100]
  rfl
theorem correct249 : interpretKey p249 = e249.denote := by
  have he : mulKey p248 p6=p249 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct6]
  rfl
theorem correct250 : interpretKey p250 = e250.denote := by
  have he : addKey p246 p249=p250 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct246,correct249]
  rfl
theorem correct251 : interpretKey p251 = e251.denote := by
  have he : mulKey p242 p66=p251 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct66]
  rfl
theorem correct252 : interpretKey p252 = e252.denote := by
  have he : mulKey p69 p83=p252 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct83]
  rfl
theorem correct253 : interpretKey p253 = e253.denote := by
  have he : addKey p251 p252=p253 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct251,correct252]
  rfl
theorem correct254 : interpretKey p254 = e254.denote := by
  have he : computeKey e254=p254 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he]; exact computeKey_correct e254
theorem correct255 : interpretKey p255 = e255.denote := by
  have he : mulKey p253 p254=p255 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct253,correct254]
  rfl
theorem correct256 : interpretKey p256 = e256.denote := by
  have he : negKey p255=p256 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct255]
  rfl
theorem correct257 : interpretKey p257 = e257.denote := by
  have he : addKey p250 p256=p257 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct250,correct256]
  rfl
theorem correct258 : interpretKey p258 = e258.denote := by
  have he : powerKey p257 2=p258 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct257]
  rfl
theorem correct259 : interpretKey p259 = e259.denote := by
  have he : mulKey p242 p27=p259 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct27]
  rfl
theorem correct260 : interpretKey p260 = e260.denote := by
  have he : mulKey p259 p49=p260 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct259,correct49]
  rfl
theorem correct261 : interpretKey p261 = e261.denote := by
  have he : mulKey p69 p74=p261 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct74]
  rfl
theorem correct262 : interpretKey p262 = e262.denote := by
  have he : addKey p260 p261=p262 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct260,correct261]
  rfl
theorem correct263 : interpretKey p263 = e263.denote := by
  have he : mulKey p248 p26=p263 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct26]
  rfl
theorem correct264 : interpretKey p264 = e264.denote := by
  have he : addKey p262 p263=p264 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct262,correct263]
  rfl
theorem correct265 : interpretKey p265 = e265.denote := by
  have he : addKey p264 p256=p265 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct264,correct256]
  rfl
theorem correct266 : interpretKey p266 = e266.denote := by
  have he : powerKey p265 2=p266 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct265]
  rfl
theorem correct267 : interpretKey p267 = e267.denote := by
  have he : mulKey p242 p32=p267 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct32]
  rfl
theorem correct268 : interpretKey p268 = e268.denote := by
  have he : mulKey p267 p49=p268 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct267,correct49]
  rfl
theorem correct269 : interpretKey p269 = e269.denote := by
  have he : mulKey p69 p75=p269 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct75]
  rfl
theorem correct270 : interpretKey p270 = e270.denote := by
  have he : addKey p268 p269=p270 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct268,correct269]
  rfl
theorem correct271 : interpretKey p271 = e271.denote := by
  have he : mulKey p248 p31=p271 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct31]
  rfl
theorem correct272 : interpretKey p272 = e272.denote := by
  have he : addKey p270 p271=p272 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct270,correct271]
  rfl
theorem correct273 : interpretKey p273 = e273.denote := by
  have he : addKey p272 p256=p273 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct272,correct256]
  rfl
theorem correct274 : interpretKey p274 = e274.denote := by
  have he : powerKey p273 2=p274 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct273]
  rfl
theorem correct275 : interpretKey p275 = e275.denote := by
  have he : mulKey p242 p37=p275 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct37]
  rfl
theorem correct276 : interpretKey p276 = e276.denote := by
  have he : mulKey p275 p49=p276 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct275,correct49]
  rfl
theorem correct277 : interpretKey p277 = e277.denote := by
  have he : mulKey p69 p76=p277 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct76]
  rfl
theorem correct278 : interpretKey p278 = e278.denote := by
  have he : addKey p276 p277=p278 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct276,correct277]
  rfl
theorem correct279 : interpretKey p279 = e279.denote := by
  have he : mulKey p248 p36=p279 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct36]
  rfl
theorem correct280 : interpretKey p280 = e280.denote := by
  have he : addKey p278 p279=p280 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct278,correct279]
  rfl
theorem correct281 : interpretKey p281 = e281.denote := by
  have he : addKey p280 p256=p281 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct280,correct256]
  rfl
theorem correct282 : interpretKey p282 = e282.denote := by
  have he : powerKey p281 2=p282 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct281]
  rfl
theorem correct283 : interpretKey p283 = e283.denote := by
  have he : mulKey p242 p41=p283 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct41]
  rfl
theorem correct284 : interpretKey p284 = e284.denote := by
  have he : mulKey p283 p49=p284 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct283,correct49]
  rfl
theorem correct285 : interpretKey p285 = e285.denote := by
  have he : mulKey p69 p77=p285 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct77]
  rfl
theorem correct286 : interpretKey p286 = e286.denote := by
  have he : addKey p284 p285=p286 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct284,correct285]
  rfl
theorem correct287 : interpretKey p287 = e287.denote := by
  have he : mulKey p248 p40=p287 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct40]
  rfl
theorem correct288 : interpretKey p288 = e288.denote := by
  have he : addKey p286 p287=p288 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct286,correct287]
  rfl
theorem correct289 : interpretKey p289 = e289.denote := by
  have he : addKey p288 p256=p289 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct288,correct256]
  rfl
theorem correct290 : interpretKey p290 = e290.denote := by
  have he : powerKey p289 2=p290 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct289]
  rfl
theorem correct291 : interpretKey p291 = e291.denote := by
  have he : mulKey p242 p44=p291 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct242,correct44]
  rfl
theorem correct292 : interpretKey p292 = e292.denote := by
  have he : mulKey p291 p49=p292 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct291,correct49]
  rfl
theorem correct293 : interpretKey p293 = e293.denote := by
  have he : mulKey p69 p78=p293 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct69,correct78]
  rfl
theorem correct294 : interpretKey p294 = e294.denote := by
  have he : addKey p292 p293=p294 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct292,correct293]
  rfl
theorem correct295 : interpretKey p295 = e295.denote := by
  have he : mulKey p248 p43=p295 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct248,correct43]
  rfl
theorem correct296 : interpretKey p296 = e296.denote := by
  have he : addKey p294 p295=p296 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct294,correct295]
  rfl
theorem correct297 : interpretKey p297 = e297.denote := by
  have he : addKey p296 p256=p297 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct296,correct256]
  rfl
theorem correct298 : interpretKey p298 = e298.denote := by
  have he : powerKey p297 2=p298 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_power,correct297]
  rfl
theorem correct299 : interpretKey p299 = e299.denote := by
  have he : addKey p290 p298=p299 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct290,correct298]
  rfl
theorem correct300 : interpretKey p300 = e300.denote := by
  have he : addKey p282 p299=p300 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct282,correct299]
  rfl
theorem correct301 : interpretKey p301 = e301.denote := by
  have he : addKey p274 p300=p301 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct274,correct300]
  rfl
theorem correct302 : interpretKey p302 = e302.denote := by
  have he : addKey p266 p301=p302 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct266,correct301]
  rfl
theorem correct303 : interpretKey p303 = e303.denote := by
  have he : addKey p258 p302=p303 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct258,correct302]
  rfl
theorem correct304 : interpretKey p304 = e304.denote := by
  have he : mulKey p241 p303=p304 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct241,correct303]
  rfl
theorem correct305 : interpretKey p305 = e305.denote := by
  have he : negKey p304=p305 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_neg,correct304]
  rfl
theorem correct306 : interpretKey p306 = e306.denote := by
  have he : addKey p240 p305=p306 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_add,correct240,correct305]
  rfl
theorem correct307 : interpretKey p307 = e307.denote := by
  have he : mulKey p237 p306=p307 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct237,correct306]
  rfl
theorem correct308 : interpretKey p308 = e308.denote := by
  have he : mulKey p0 p307=p308 := keyPolyEqual_sound _ _ (by decide +kernel)
  rw [← he,interpretKey_mul,correct0,correct307]
  rfl
theorem entryQ_raw : interpretKey p308 = e308.denote := correct308
end R7.Core.SpectralCoefficient.Expansion
