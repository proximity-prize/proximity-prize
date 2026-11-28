import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_e9774b3fc07c89e3
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da

section Pack_Z6970H2307PackedBand28Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid28_342 : thresholds28_342.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_342 (by decide +kernel)

theorem valid28_348 : thresholds28_348.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_348 (by decide +kernel)

theorem valid28_354 : thresholds28_354.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_354 (by decide +kernel)

theorem valid28_360 : thresholds28_360.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_360 (by decide +kernel)

theorem valid28_366 : thresholds28_366.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_366 (by decide +kernel)

theorem valid28_372 : thresholds28_372.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_372 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand28Part003

section Pack_Z6970H2307PackedBand29Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid29_0_0 : (thresholds29_0.take 4).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_0.take 4) (by decide +kernel)

private theorem valid29_0_4 : (thresholds29_0.drop 4).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_0.drop 4) (by decide +kernel)

theorem valid29_0 : thresholds29_0.all (checked ⟨3,7,1⟩)=true :=
  all_take_drop (checked ⟨3,7,1⟩) thresholds29_0 4 valid29_0_0 (valid29_0_4)

theorem valid29_6 : thresholds29_6.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_6 (by decide +kernel)

theorem valid29_12 : thresholds29_12.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_12 (by decide +kernel)

theorem valid29_18 : thresholds29_18.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_18 (by decide +kernel)

private theorem valid29_24_0 : (thresholds29_24.take 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_24.take 5) (by decide +kernel)

private theorem valid29_24_5 : (thresholds29_24.drop 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_24.drop 5) (by decide +kernel)

theorem valid29_24 : thresholds29_24.all (checked ⟨3,7,1⟩)=true :=
  all_take_drop (checked ⟨3,7,1⟩) thresholds29_24 5 valid29_24_0 (valid29_24_5)

private theorem valid29_30_0 : (thresholds29_30.take 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_30.take 5) (by decide +kernel)

private theorem valid29_30_5 : (thresholds29_30.drop 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_30.drop 5) (by decide +kernel)

theorem valid29_30 : thresholds29_30.all (checked ⟨3,7,1⟩)=true :=
  all_take_drop (checked ⟨3,7,1⟩) thresholds29_30 5 valid29_30_0 (valid29_30_5)

theorem valid29_36 : thresholds29_36.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_36 (by decide +kernel)

theorem valid29_42 : thresholds29_42.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_42 (by decide +kernel)

theorem valid29_48 : thresholds29_48.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_48 (by decide +kernel)

theorem valid29_54 : thresholds29_54.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_54 (by decide +kernel)

private theorem valid29_60_0 : (thresholds29_60.take 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_60.take 5) (by decide +kernel)

private theorem valid29_60_5 : (thresholds29_60.drop 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_60.drop 5) (by decide +kernel)

theorem valid29_60 : thresholds29_60.all (checked ⟨3,7,1⟩)=true :=
  all_take_drop (checked ⟨3,7,1⟩) thresholds29_60 5 valid29_60_0 (valid29_60_5)

theorem valid29_66 : thresholds29_66.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_66 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand29Part000

section Pack_Z6970H2307PackedBand29Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid29_72 : thresholds29_72.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_72 (by decide +kernel)

private theorem valid29_78_0 : (thresholds29_78.take 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_78.take 5) (by decide +kernel)

private theorem valid29_78_5 : (thresholds29_78.drop 5).all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 (thresholds29_78.drop 5) (by decide +kernel)

theorem valid29_78 : thresholds29_78.all (checked ⟨3,7,1⟩)=true :=
  all_take_drop (checked ⟨3,7,1⟩) thresholds29_78 5 valid29_78_0 (valid29_78_5)

theorem valid29_84 : thresholds29_84.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_84 (by decide +kernel)

theorem valid29_90 : thresholds29_90.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_90 (by decide +kernel)

theorem valid29_96 : thresholds29_96.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_96 (by decide +kernel)

theorem valid29_102 : thresholds29_102.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_102 (by decide +kernel)

theorem valid29_108 : thresholds29_108.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_108 (by decide +kernel)

theorem valid29_114 : thresholds29_114.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_114 (by decide +kernel)

theorem valid29_120 : thresholds29_120.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_120 (by decide +kernel)

theorem valid29_126 : thresholds29_126.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_126 (by decide +kernel)

theorem valid29_132 : thresholds29_132.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_132 (by decide +kernel)

theorem valid29_138 : thresholds29_138.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_138 (by decide +kernel)

theorem valid29_144 : thresholds29_144.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_144 (by decide +kernel)

theorem valid29_150 : thresholds29_150.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_150 (by decide +kernel)

theorem valid29_156 : thresholds29_156.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_156 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand29Part001

section Pack_Z6970H2307PackedBand29Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid29_162 : thresholds29_162.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_162 (by decide +kernel)

theorem valid29_168 : thresholds29_168.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_168 (by decide +kernel)

theorem valid29_174 : thresholds29_174.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_174 (by decide +kernel)

theorem valid29_180 : thresholds29_180.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_180 (by decide +kernel)

theorem valid29_186 : thresholds29_186.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_186 (by decide +kernel)

theorem valid29_192 : thresholds29_192.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_192 (by decide +kernel)

theorem valid29_198 : thresholds29_198.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_198 (by decide +kernel)

theorem valid29_204 : thresholds29_204.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_204 (by decide +kernel)

theorem valid29_210 : thresholds29_210.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_210 (by decide +kernel)

theorem valid29_216 : thresholds29_216.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_216 (by decide +kernel)

theorem valid29_222 : thresholds29_222.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_222 (by decide +kernel)

theorem valid29_228 : thresholds29_228.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_228 (by decide +kernel)

theorem valid29_234 : thresholds29_234.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_234 (by decide +kernel)

theorem valid29_240 : thresholds29_240.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_240 (by decide +kernel)

theorem valid29_246 : thresholds29_246.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_246 (by decide +kernel)

theorem valid29_252 : thresholds29_252.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_252 (by decide +kernel)

theorem valid29_258 : thresholds29_258.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_258 (by decide +kernel)

theorem valid29_264 : thresholds29_264.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_264 (by decide +kernel)

theorem valid29_270 : thresholds29_270.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_270 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand29Part002

section Pack_Z6970H2307PackedBand29Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid29_276 : thresholds29_276.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_276 (by decide +kernel)

theorem valid29_282 : thresholds29_282.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_282 (by decide +kernel)

theorem valid29_288 : thresholds29_288.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_288 (by decide +kernel)

theorem valid29_294 : thresholds29_294.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_294 (by decide +kernel)

theorem valid29_300 : thresholds29_300.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_300 (by decide +kernel)

theorem valid29_306 : thresholds29_306.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_306 (by decide +kernel)

theorem valid29_312 : thresholds29_312.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_312 (by decide +kernel)

theorem valid29_318 : thresholds29_318.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_318 (by decide +kernel)

theorem valid29_324 : thresholds29_324.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_324 (by decide +kernel)

theorem valid29_330 : thresholds29_330.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_330 (by decide +kernel)

theorem valid29_336 : thresholds29_336.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_336 (by decide +kernel)

theorem valid29_342 : thresholds29_342.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_342 (by decide +kernel)

theorem valid29_348 : thresholds29_348.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_348 (by decide +kernel)

theorem valid29_354 : thresholds29_354.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_354 (by decide +kernel)

theorem valid29_360 : thresholds29_360.all (checked ⟨3,7,1⟩)=true :=
  checkedVerified ⟨3,7,1⟩ prefixMap29 thresholds29_360 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand29Part003

section Pack_Z6970H2307PackedBand30Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid30_0_0 : (thresholds30_0.take 4).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_0.take 4) (by decide +kernel)

private theorem valid30_0_4 : (thresholds30_0.drop 4).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_0.drop 4) (by decide +kernel)

theorem valid30_0 : thresholds30_0.all (checked ⟨3,7,2⟩)=true :=
  all_take_drop (checked ⟨3,7,2⟩) thresholds30_0 4 valid30_0_0 (valid30_0_4)

theorem valid30_6 : thresholds30_6.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_6 (by decide +kernel)

theorem valid30_12 : thresholds30_12.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_12 (by decide +kernel)

theorem valid30_18 : thresholds30_18.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_18 (by decide +kernel)

private theorem valid30_24_0 : (thresholds30_24.take 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_24.take 5) (by decide +kernel)

private theorem valid30_24_5 : (thresholds30_24.drop 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_24.drop 5) (by decide +kernel)

theorem valid30_24 : thresholds30_24.all (checked ⟨3,7,2⟩)=true :=
  all_take_drop (checked ⟨3,7,2⟩) thresholds30_24 5 valid30_24_0 (valid30_24_5)

private theorem valid30_30_0 : (thresholds30_30.take 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_30.take 5) (by decide +kernel)

private theorem valid30_30_5 : (thresholds30_30.drop 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_30.drop 5) (by decide +kernel)

theorem valid30_30 : thresholds30_30.all (checked ⟨3,7,2⟩)=true :=
  all_take_drop (checked ⟨3,7,2⟩) thresholds30_30 5 valid30_30_0 (valid30_30_5)

theorem valid30_36 : thresholds30_36.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_36 (by decide +kernel)

theorem valid30_42 : thresholds30_42.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_42 (by decide +kernel)

theorem valid30_48 : thresholds30_48.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_48 (by decide +kernel)

theorem valid30_54 : thresholds30_54.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_54 (by decide +kernel)

private theorem valid30_60_0 : (thresholds30_60.take 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_60.take 5) (by decide +kernel)

private theorem valid30_60_5 : (thresholds30_60.drop 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_60.drop 5) (by decide +kernel)

theorem valid30_60 : thresholds30_60.all (checked ⟨3,7,2⟩)=true :=
  all_take_drop (checked ⟨3,7,2⟩) thresholds30_60 5 valid30_60_0 (valid30_60_5)

theorem valid30_66 : thresholds30_66.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_66 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand30Part000

section Pack_Z6970H2307PackedBand30Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid30_72 : thresholds30_72.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_72 (by decide +kernel)

private theorem valid30_78_0 : (thresholds30_78.take 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_78.take 5) (by decide +kernel)

private theorem valid30_78_5 : (thresholds30_78.drop 5).all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 (thresholds30_78.drop 5) (by decide +kernel)

theorem valid30_78 : thresholds30_78.all (checked ⟨3,7,2⟩)=true :=
  all_take_drop (checked ⟨3,7,2⟩) thresholds30_78 5 valid30_78_0 (valid30_78_5)

theorem valid30_84 : thresholds30_84.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_84 (by decide +kernel)

theorem valid30_90 : thresholds30_90.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_90 (by decide +kernel)

theorem valid30_96 : thresholds30_96.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_96 (by decide +kernel)

theorem valid30_102 : thresholds30_102.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_102 (by decide +kernel)

theorem valid30_108 : thresholds30_108.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_108 (by decide +kernel)

theorem valid30_114 : thresholds30_114.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_114 (by decide +kernel)

theorem valid30_120 : thresholds30_120.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_120 (by decide +kernel)

theorem valid30_126 : thresholds30_126.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_126 (by decide +kernel)

theorem valid30_132 : thresholds30_132.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_132 (by decide +kernel)

theorem valid30_138 : thresholds30_138.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_138 (by decide +kernel)

theorem valid30_144 : thresholds30_144.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_144 (by decide +kernel)

theorem valid30_150 : thresholds30_150.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_150 (by decide +kernel)

theorem valid30_156 : thresholds30_156.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_156 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand30Part001

section Pack_Z6970H2307PackedBand30Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid30_162 : thresholds30_162.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_162 (by decide +kernel)

theorem valid30_168 : thresholds30_168.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_168 (by decide +kernel)

theorem valid30_174 : thresholds30_174.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_174 (by decide +kernel)

theorem valid30_180 : thresholds30_180.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_180 (by decide +kernel)

theorem valid30_186 : thresholds30_186.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_186 (by decide +kernel)

theorem valid30_192 : thresholds30_192.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_192 (by decide +kernel)

theorem valid30_198 : thresholds30_198.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_198 (by decide +kernel)

theorem valid30_204 : thresholds30_204.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_204 (by decide +kernel)

theorem valid30_210 : thresholds30_210.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_210 (by decide +kernel)

theorem valid30_216 : thresholds30_216.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_216 (by decide +kernel)

theorem valid30_222 : thresholds30_222.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_222 (by decide +kernel)

theorem valid30_228 : thresholds30_228.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_228 (by decide +kernel)

theorem valid30_234 : thresholds30_234.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_234 (by decide +kernel)

theorem valid30_240 : thresholds30_240.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_240 (by decide +kernel)

theorem valid30_246 : thresholds30_246.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_246 (by decide +kernel)

theorem valid30_252 : thresholds30_252.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_252 (by decide +kernel)

theorem valid30_258 : thresholds30_258.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_258 (by decide +kernel)

theorem valid30_264 : thresholds30_264.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_264 (by decide +kernel)

theorem valid30_270 : thresholds30_270.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_270 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand30Part002

section Pack_Z6970H2307PackedBand30Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid30_276 : thresholds30_276.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_276 (by decide +kernel)

theorem valid30_282 : thresholds30_282.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_282 (by decide +kernel)

theorem valid30_288 : thresholds30_288.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_288 (by decide +kernel)

theorem valid30_294 : thresholds30_294.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_294 (by decide +kernel)

theorem valid30_300 : thresholds30_300.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_300 (by decide +kernel)

theorem valid30_306 : thresholds30_306.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_306 (by decide +kernel)

theorem valid30_312 : thresholds30_312.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_312 (by decide +kernel)

theorem valid30_318 : thresholds30_318.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_318 (by decide +kernel)

theorem valid30_324 : thresholds30_324.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_324 (by decide +kernel)

theorem valid30_330 : thresholds30_330.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_330 (by decide +kernel)

theorem valid30_336 : thresholds30_336.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_336 (by decide +kernel)

theorem valid30_342 : thresholds30_342.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_342 (by decide +kernel)

theorem valid30_348 : thresholds30_348.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_348 (by decide +kernel)

theorem valid30_354 : thresholds30_354.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_354 (by decide +kernel)

theorem valid30_360 : thresholds30_360.all (checked ⟨3,7,2⟩)=true :=
  checkedVerified ⟨3,7,2⟩ prefixMap30 thresholds30_360 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand30Part003

section Pack_Z6970H2307PackedBand31Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid31_0 : thresholds31_0.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_0 (by decide +kernel)

theorem valid31_6 : thresholds31_6.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_6 (by decide +kernel)

theorem valid31_12 : thresholds31_12.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_12 (by decide +kernel)

theorem valid31_18 : thresholds31_18.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_18 (by decide +kernel)

theorem valid31_24 : thresholds31_24.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_24 (by decide +kernel)

theorem valid31_30 : thresholds31_30.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_30 (by decide +kernel)

theorem valid31_36 : thresholds31_36.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_36 (by decide +kernel)

private theorem valid31_42_0 : (thresholds31_42.take 5).all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 (thresholds31_42.take 5) (by decide +kernel)

private theorem valid31_42_5 : (thresholds31_42.drop 5).all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 (thresholds31_42.drop 5) (by decide +kernel)

theorem valid31_42 : thresholds31_42.all (checked ⟨6,7,2⟩)=true :=
  all_take_drop (checked ⟨6,7,2⟩) thresholds31_42 5 valid31_42_0 (valid31_42_5)

theorem valid31_48 : thresholds31_48.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_48 (by decide +kernel)

theorem valid31_54 : thresholds31_54.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_54 (by decide +kernel)

theorem valid31_60 : thresholds31_60.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_60 (by decide +kernel)

theorem valid31_66 : thresholds31_66.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_66 (by decide +kernel)

theorem valid31_72 : thresholds31_72.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_72 (by decide +kernel)

theorem valid31_78 : thresholds31_78.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_78 (by decide +kernel)

theorem valid31_84 : thresholds31_84.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_84 (by decide +kernel)

theorem valid31_90 : thresholds31_90.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_90 (by decide +kernel)

theorem valid31_96 : thresholds31_96.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand31Part000

section Pack_Z6970H2307PackedBand31Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid31_102 : thresholds31_102.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_102 (by decide +kernel)

theorem valid31_108 : thresholds31_108.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_108 (by decide +kernel)

theorem valid31_114 : thresholds31_114.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_114 (by decide +kernel)

theorem valid31_120 : thresholds31_120.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_120 (by decide +kernel)

theorem valid31_126 : thresholds31_126.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_126 (by decide +kernel)

theorem valid31_132 : thresholds31_132.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_132 (by decide +kernel)

theorem valid31_138 : thresholds31_138.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_138 (by decide +kernel)

theorem valid31_144 : thresholds31_144.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_144 (by decide +kernel)

theorem valid31_150 : thresholds31_150.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_150 (by decide +kernel)

theorem valid31_156 : thresholds31_156.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_156 (by decide +kernel)

theorem valid31_162 : thresholds31_162.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_162 (by decide +kernel)

theorem valid31_168 : thresholds31_168.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_168 (by decide +kernel)

theorem valid31_174 : thresholds31_174.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_174 (by decide +kernel)

theorem valid31_180 : thresholds31_180.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_180 (by decide +kernel)

theorem valid31_186 : thresholds31_186.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_186 (by decide +kernel)

theorem valid31_192 : thresholds31_192.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_192 (by decide +kernel)

theorem valid31_198 : thresholds31_198.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_198 (by decide +kernel)

theorem valid31_204 : thresholds31_204.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_204 (by decide +kernel)

theorem valid31_210 : thresholds31_210.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_210 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand31Part001

section Pack_Z6970H2307PackedBand31Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid31_216 : thresholds31_216.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_216 (by decide +kernel)

theorem valid31_222 : thresholds31_222.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_222 (by decide +kernel)

theorem valid31_228 : thresholds31_228.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_228 (by decide +kernel)

theorem valid31_234 : thresholds31_234.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_234 (by decide +kernel)

theorem valid31_240 : thresholds31_240.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_240 (by decide +kernel)

theorem valid31_246 : thresholds31_246.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_246 (by decide +kernel)

theorem valid31_252 : thresholds31_252.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_252 (by decide +kernel)

theorem valid31_258 : thresholds31_258.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_258 (by decide +kernel)

theorem valid31_264 : thresholds31_264.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_264 (by decide +kernel)

theorem valid31_270 : thresholds31_270.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_270 (by decide +kernel)

theorem valid31_276 : thresholds31_276.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_276 (by decide +kernel)

theorem valid31_282 : thresholds31_282.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_282 (by decide +kernel)

theorem valid31_288 : thresholds31_288.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_288 (by decide +kernel)

theorem valid31_294 : thresholds31_294.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_294 (by decide +kernel)

theorem valid31_300 : thresholds31_300.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_300 (by decide +kernel)

theorem valid31_306 : thresholds31_306.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_306 (by decide +kernel)

theorem valid31_312 : thresholds31_312.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_312 (by decide +kernel)

theorem valid31_318 : thresholds31_318.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_318 (by decide +kernel)

theorem valid31_324 : thresholds31_324.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_324 (by decide +kernel)

theorem valid31_330 : thresholds31_330.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_330 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand31Part002

section Pack_Z6970H2307PackedBand31Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid31_336 : thresholds31_336.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_336 (by decide +kernel)

theorem valid31_342 : thresholds31_342.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_342 (by decide +kernel)

theorem valid31_348 : thresholds31_348.all (checked ⟨6,7,2⟩)=true :=
  checkedVerified ⟨6,7,2⟩ prefixMap31 thresholds31_348 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand31Part003

section Pack_Z6970H2307PackedBand32Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid32_0 : thresholds32_0.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_0 (by decide +kernel)

theorem valid32_6 : thresholds32_6.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_6 (by decide +kernel)

theorem valid32_12 : thresholds32_12.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_12 (by decide +kernel)

theorem valid32_18 : thresholds32_18.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_18 (by decide +kernel)

private theorem valid32_24_0 : (thresholds32_24.take 5).all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 (thresholds32_24.take 5) (by decide +kernel)

private theorem valid32_24_5 : (thresholds32_24.drop 5).all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 (thresholds32_24.drop 5) (by decide +kernel)

theorem valid32_24 : thresholds32_24.all (checked ⟨9,7,2⟩)=true :=
  all_take_drop (checked ⟨9,7,2⟩) thresholds32_24 5 valid32_24_0 (valid32_24_5)

theorem valid32_30 : thresholds32_30.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_30 (by decide +kernel)

theorem valid32_36 : thresholds32_36.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_36 (by decide +kernel)

theorem valid32_42 : thresholds32_42.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_42 (by decide +kernel)

theorem valid32_48 : thresholds32_48.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_48 (by decide +kernel)

theorem valid32_54 : thresholds32_54.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_54 (by decide +kernel)

theorem valid32_60 : thresholds32_60.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_60 (by decide +kernel)

private theorem valid32_66_0 : (thresholds32_66.take 5).all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 (thresholds32_66.take 5) (by decide +kernel)

private theorem valid32_66_5 : (thresholds32_66.drop 5).all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 (thresholds32_66.drop 5) (by decide +kernel)

theorem valid32_66 : thresholds32_66.all (checked ⟨9,7,2⟩)=true :=
  all_take_drop (checked ⟨9,7,2⟩) thresholds32_66 5 valid32_66_0 (valid32_66_5)

theorem valid32_72 : thresholds32_72.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_72 (by decide +kernel)

theorem valid32_78 : thresholds32_78.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_78 (by decide +kernel)

theorem valid32_84 : thresholds32_84.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_84 (by decide +kernel)

theorem valid32_90 : thresholds32_90.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_90 (by decide +kernel)

theorem valid32_96 : thresholds32_96.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_96 (by decide +kernel)

theorem valid32_102 : thresholds32_102.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_102 (by decide +kernel)

theorem valid32_108 : thresholds32_108.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_108 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand32Part000

section Pack_Z6970H2307PackedBand32Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid32_114 : thresholds32_114.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_114 (by decide +kernel)

theorem valid32_120 : thresholds32_120.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_120 (by decide +kernel)

theorem valid32_126 : thresholds32_126.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_126 (by decide +kernel)

theorem valid32_132 : thresholds32_132.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_132 (by decide +kernel)

theorem valid32_138 : thresholds32_138.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_138 (by decide +kernel)

theorem valid32_144 : thresholds32_144.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_144 (by decide +kernel)

theorem valid32_150 : thresholds32_150.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_150 (by decide +kernel)

theorem valid32_156 : thresholds32_156.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_156 (by decide +kernel)

theorem valid32_162 : thresholds32_162.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_162 (by decide +kernel)

theorem valid32_168 : thresholds32_168.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_168 (by decide +kernel)

theorem valid32_174 : thresholds32_174.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_174 (by decide +kernel)

theorem valid32_180 : thresholds32_180.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_180 (by decide +kernel)

theorem valid32_186 : thresholds32_186.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_186 (by decide +kernel)

theorem valid32_192 : thresholds32_192.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_192 (by decide +kernel)

theorem valid32_198 : thresholds32_198.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_198 (by decide +kernel)

theorem valid32_204 : thresholds32_204.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_204 (by decide +kernel)

theorem valid32_210 : thresholds32_210.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_210 (by decide +kernel)

theorem valid32_216 : thresholds32_216.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_216 (by decide +kernel)

theorem valid32_222 : thresholds32_222.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_222 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand32Part001

section Pack_Z6970H2307PackedBand32Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid32_228 : thresholds32_228.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_228 (by decide +kernel)

theorem valid32_234 : thresholds32_234.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_234 (by decide +kernel)

theorem valid32_240 : thresholds32_240.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_240 (by decide +kernel)

theorem valid32_246 : thresholds32_246.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_246 (by decide +kernel)

theorem valid32_252 : thresholds32_252.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_252 (by decide +kernel)

theorem valid32_258 : thresholds32_258.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_258 (by decide +kernel)

theorem valid32_264 : thresholds32_264.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_264 (by decide +kernel)

theorem valid32_270 : thresholds32_270.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_270 (by decide +kernel)

theorem valid32_276 : thresholds32_276.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_276 (by decide +kernel)

theorem valid32_282 : thresholds32_282.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_282 (by decide +kernel)

theorem valid32_288 : thresholds32_288.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_288 (by decide +kernel)

theorem valid32_294 : thresholds32_294.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_294 (by decide +kernel)

theorem valid32_300 : thresholds32_300.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_300 (by decide +kernel)

theorem valid32_306 : thresholds32_306.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_306 (by decide +kernel)

theorem valid32_312 : thresholds32_312.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_312 (by decide +kernel)

theorem valid32_318 : thresholds32_318.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_318 (by decide +kernel)

theorem valid32_324 : thresholds32_324.all (checked ⟨9,7,2⟩)=true :=
  checkedVerified ⟨9,7,2⟩ prefixMap32 thresholds32_324 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand32Part002

section Pack_Z6970H2307PackedBand33Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid33_0 : thresholds33_0.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_0 (by decide +kernel)

theorem valid33_6 : thresholds33_6.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_6 (by decide +kernel)

theorem valid33_12 : thresholds33_12.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_12 (by decide +kernel)

theorem valid33_18 : thresholds33_18.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_18 (by decide +kernel)

theorem valid33_24 : thresholds33_24.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_24 (by decide +kernel)

theorem valid33_30 : thresholds33_30.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_30 (by decide +kernel)

theorem valid33_36 : thresholds33_36.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_36 (by decide +kernel)

theorem valid33_42 : thresholds33_42.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_42 (by decide +kernel)

theorem valid33_48 : thresholds33_48.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_48 (by decide +kernel)

theorem valid33_54 : thresholds33_54.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_54 (by decide +kernel)

theorem valid33_60 : thresholds33_60.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_60 (by decide +kernel)

theorem valid33_66 : thresholds33_66.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_66 (by decide +kernel)

theorem valid33_72 : thresholds33_72.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_72 (by decide +kernel)

theorem valid33_78 : thresholds33_78.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_78 (by decide +kernel)

theorem valid33_84 : thresholds33_84.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_84 (by decide +kernel)

theorem valid33_90 : thresholds33_90.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_90 (by decide +kernel)

theorem valid33_96 : thresholds33_96.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_96 (by decide +kernel)

theorem valid33_102 : thresholds33_102.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_102 (by decide +kernel)

theorem valid33_108 : thresholds33_108.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_108 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand33Part000

section Pack_Z6970H2307PackedBand33Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid33_114 : thresholds33_114.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_114 (by decide +kernel)

theorem valid33_120 : thresholds33_120.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_120 (by decide +kernel)

theorem valid33_126 : thresholds33_126.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_126 (by decide +kernel)

theorem valid33_132 : thresholds33_132.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_132 (by decide +kernel)

theorem valid33_138 : thresholds33_138.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_138 (by decide +kernel)

theorem valid33_144 : thresholds33_144.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_144 (by decide +kernel)

theorem valid33_150 : thresholds33_150.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_150 (by decide +kernel)

theorem valid33_156 : thresholds33_156.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_156 (by decide +kernel)

theorem valid33_162 : thresholds33_162.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_162 (by decide +kernel)

theorem valid33_168 : thresholds33_168.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_168 (by decide +kernel)

theorem valid33_174 : thresholds33_174.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_174 (by decide +kernel)

theorem valid33_180 : thresholds33_180.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_180 (by decide +kernel)

theorem valid33_186 : thresholds33_186.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_186 (by decide +kernel)

theorem valid33_192 : thresholds33_192.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_192 (by decide +kernel)

theorem valid33_198 : thresholds33_198.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_198 (by decide +kernel)

theorem valid33_204 : thresholds33_204.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_204 (by decide +kernel)

theorem valid33_210 : thresholds33_210.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_210 (by decide +kernel)

theorem valid33_216 : thresholds33_216.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_216 (by decide +kernel)

theorem valid33_222 : thresholds33_222.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_222 (by decide +kernel)

theorem valid33_228 : thresholds33_228.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_228 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand33Part001

section Pack_Z6970H2307PackedBand33Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid33_234 : thresholds33_234.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_234 (by decide +kernel)

theorem valid33_240 : thresholds33_240.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_240 (by decide +kernel)

theorem valid33_246 : thresholds33_246.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_246 (by decide +kernel)

theorem valid33_252 : thresholds33_252.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_252 (by decide +kernel)

theorem valid33_258 : thresholds33_258.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_258 (by decide +kernel)

theorem valid33_264 : thresholds33_264.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_264 (by decide +kernel)

theorem valid33_270 : thresholds33_270.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_270 (by decide +kernel)

theorem valid33_276 : thresholds33_276.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_276 (by decide +kernel)

theorem valid33_282 : thresholds33_282.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_282 (by decide +kernel)

theorem valid33_288 : thresholds33_288.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_288 (by decide +kernel)

theorem valid33_294 : thresholds33_294.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_294 (by decide +kernel)

theorem valid33_300 : thresholds33_300.all (checked ⟨11,7,2⟩)=true :=
  checkedVerified ⟨11,7,2⟩ prefixMap33 thresholds33_300 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand33Part002

section Pack_Z6970H2307PackedBand34Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid34_0 : thresholds34_0.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_0 (by decide +kernel)

theorem valid34_6 : thresholds34_6.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_6 (by decide +kernel)

theorem valid34_12 : thresholds34_12.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_12 (by decide +kernel)

theorem valid34_18 : thresholds34_18.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_18 (by decide +kernel)

theorem valid34_24 : thresholds34_24.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_24 (by decide +kernel)

theorem valid34_30 : thresholds34_30.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_30 (by decide +kernel)

theorem valid34_36 : thresholds34_36.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_36 (by decide +kernel)

theorem valid34_42 : thresholds34_42.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_42 (by decide +kernel)

theorem valid34_48 : thresholds34_48.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_48 (by decide +kernel)

theorem valid34_54 : thresholds34_54.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_54 (by decide +kernel)

theorem valid34_60 : thresholds34_60.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_60 (by decide +kernel)

theorem valid34_66 : thresholds34_66.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_66 (by decide +kernel)

theorem valid34_72 : thresholds34_72.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_72 (by decide +kernel)

theorem valid34_78 : thresholds34_78.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_78 (by decide +kernel)

theorem valid34_84 : thresholds34_84.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_84 (by decide +kernel)

theorem valid34_90 : thresholds34_90.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_90 (by decide +kernel)

theorem valid34_96 : thresholds34_96.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_96 (by decide +kernel)

theorem valid34_102 : thresholds34_102.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_102 (by decide +kernel)

theorem valid34_108 : thresholds34_108.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_108 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand34Part000

section Pack_Z6970H2307PackedBand34Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid34_114 : thresholds34_114.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_114 (by decide +kernel)

theorem valid34_120 : thresholds34_120.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_120 (by decide +kernel)

theorem valid34_126 : thresholds34_126.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_126 (by decide +kernel)

theorem valid34_132 : thresholds34_132.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_132 (by decide +kernel)

theorem valid34_138 : thresholds34_138.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_138 (by decide +kernel)

theorem valid34_144 : thresholds34_144.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_144 (by decide +kernel)

theorem valid34_150 : thresholds34_150.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_150 (by decide +kernel)

theorem valid34_156 : thresholds34_156.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_156 (by decide +kernel)

theorem valid34_162 : thresholds34_162.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_162 (by decide +kernel)

theorem valid34_168 : thresholds34_168.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_168 (by decide +kernel)

theorem valid34_174 : thresholds34_174.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_174 (by decide +kernel)

theorem valid34_180 : thresholds34_180.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_180 (by decide +kernel)

theorem valid34_186 : thresholds34_186.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_186 (by decide +kernel)

theorem valid34_192 : thresholds34_192.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_192 (by decide +kernel)

theorem valid34_198 : thresholds34_198.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_198 (by decide +kernel)

theorem valid34_204 : thresholds34_204.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_204 (by decide +kernel)

theorem valid34_210 : thresholds34_210.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_210 (by decide +kernel)

theorem valid34_216 : thresholds34_216.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_216 (by decide +kernel)

theorem valid34_222 : thresholds34_222.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_222 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand34Part001

section Pack_Z6970H2307PackedBand34Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid34_228 : thresholds34_228.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_228 (by decide +kernel)

theorem valid34_234 : thresholds34_234.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_234 (by decide +kernel)

theorem valid34_240 : thresholds34_240.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_240 (by decide +kernel)

theorem valid34_246 : thresholds34_246.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_246 (by decide +kernel)

theorem valid34_252 : thresholds34_252.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_252 (by decide +kernel)

theorem valid34_258 : thresholds34_258.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_258 (by decide +kernel)

theorem valid34_264 : thresholds34_264.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_264 (by decide +kernel)

theorem valid34_270 : thresholds34_270.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_270 (by decide +kernel)

theorem valid34_276 : thresholds34_276.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_276 (by decide +kernel)

theorem valid34_282 : thresholds34_282.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_282 (by decide +kernel)

theorem valid34_288 : thresholds34_288.all (checked ⟨12,7,2⟩)=true :=
  checkedVerified ⟨12,7,2⟩ prefixMap34 thresholds34_288 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand34Part002

section Pack_Z6970H2307PackedBand35Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid35_0 : thresholds35_0.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_0 (by decide +kernel)

theorem valid35_6 : thresholds35_6.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_6 (by decide +kernel)

theorem valid35_12 : thresholds35_12.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_12 (by decide +kernel)

theorem valid35_18 : thresholds35_18.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_18 (by decide +kernel)

theorem valid35_24 : thresholds35_24.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_24 (by decide +kernel)

theorem valid35_30 : thresholds35_30.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_30 (by decide +kernel)

theorem valid35_36 : thresholds35_36.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_36 (by decide +kernel)

theorem valid35_42 : thresholds35_42.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_42 (by decide +kernel)

theorem valid35_48 : thresholds35_48.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_48 (by decide +kernel)

theorem valid35_54 : thresholds35_54.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_54 (by decide +kernel)

theorem valid35_60 : thresholds35_60.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_60 (by decide +kernel)

theorem valid35_66 : thresholds35_66.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_66 (by decide +kernel)

theorem valid35_72 : thresholds35_72.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_72 (by decide +kernel)

theorem valid35_78 : thresholds35_78.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_78 (by decide +kernel)

theorem valid35_84 : thresholds35_84.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_84 (by decide +kernel)

theorem valid35_90 : thresholds35_90.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_90 (by decide +kernel)

theorem valid35_96 : thresholds35_96.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_96 (by decide +kernel)

theorem valid35_102 : thresholds35_102.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_102 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand35Part000

section Pack_Z6970H2307PackedBand35Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid35_108 : thresholds35_108.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_108 (by decide +kernel)

theorem valid35_114 : thresholds35_114.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_114 (by decide +kernel)

theorem valid35_120 : thresholds35_120.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_120 (by decide +kernel)

theorem valid35_126 : thresholds35_126.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_126 (by decide +kernel)

theorem valid35_132 : thresholds35_132.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_132 (by decide +kernel)

theorem valid35_138 : thresholds35_138.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_138 (by decide +kernel)

theorem valid35_144 : thresholds35_144.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_144 (by decide +kernel)

theorem valid35_150 : thresholds35_150.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_150 (by decide +kernel)

theorem valid35_156 : thresholds35_156.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_156 (by decide +kernel)

theorem valid35_162 : thresholds35_162.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_162 (by decide +kernel)

theorem valid35_168 : thresholds35_168.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_168 (by decide +kernel)

theorem valid35_174 : thresholds35_174.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_174 (by decide +kernel)

theorem valid35_180 : thresholds35_180.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_180 (by decide +kernel)

theorem valid35_186 : thresholds35_186.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_186 (by decide +kernel)

theorem valid35_192 : thresholds35_192.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_192 (by decide +kernel)

theorem valid35_198 : thresholds35_198.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_198 (by decide +kernel)

theorem valid35_204 : thresholds35_204.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_204 (by decide +kernel)

theorem valid35_210 : thresholds35_210.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_210 (by decide +kernel)

theorem valid35_216 : thresholds35_216.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_216 (by decide +kernel)

theorem valid35_222 : thresholds35_222.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_222 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand35Part001

section Pack_Z6970H2307PackedBand35Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid35_228 : thresholds35_228.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_228 (by decide +kernel)

theorem valid35_234 : thresholds35_234.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_234 (by decide +kernel)

theorem valid35_240 : thresholds35_240.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_240 (by decide +kernel)

theorem valid35_246 : thresholds35_246.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_246 (by decide +kernel)

theorem valid35_252 : thresholds35_252.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_252 (by decide +kernel)

theorem valid35_258 : thresholds35_258.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_258 (by decide +kernel)

theorem valid35_264 : thresholds35_264.all (checked ⟨13,7,2⟩)=true :=
  checkedVerified ⟨13,7,2⟩ prefixMap35 thresholds35_264 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand35Part002

section Pack_Z6970H2307PackedBand36Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid36_0 : thresholds36_0.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_0 (by decide +kernel)

theorem valid36_6 : thresholds36_6.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_6 (by decide +kernel)

theorem valid36_12 : thresholds36_12.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_12 (by decide +kernel)

theorem valid36_18 : thresholds36_18.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_18 (by decide +kernel)

theorem valid36_24 : thresholds36_24.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_24 (by decide +kernel)

theorem valid36_30 : thresholds36_30.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_30 (by decide +kernel)

theorem valid36_36 : thresholds36_36.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_36 (by decide +kernel)

theorem valid36_42 : thresholds36_42.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_42 (by decide +kernel)

theorem valid36_48 : thresholds36_48.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_48 (by decide +kernel)

theorem valid36_54 : thresholds36_54.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_54 (by decide +kernel)

theorem valid36_60 : thresholds36_60.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_60 (by decide +kernel)

theorem valid36_66 : thresholds36_66.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_66 (by decide +kernel)

theorem valid36_72 : thresholds36_72.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_72 (by decide +kernel)

theorem valid36_78 : thresholds36_78.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_78 (by decide +kernel)

theorem valid36_84 : thresholds36_84.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_84 (by decide +kernel)

theorem valid36_90 : thresholds36_90.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_90 (by decide +kernel)

theorem valid36_96 : thresholds36_96.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_96 (by decide +kernel)

theorem valid36_102 : thresholds36_102.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_102 (by decide +kernel)

theorem valid36_108 : thresholds36_108.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_108 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand36Part000

section Pack_Z6970H2307PackedBand36Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid36_114 : thresholds36_114.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_114 (by decide +kernel)

theorem valid36_120 : thresholds36_120.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_120 (by decide +kernel)

theorem valid36_126 : thresholds36_126.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_126 (by decide +kernel)

theorem valid36_132 : thresholds36_132.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_132 (by decide +kernel)

theorem valid36_138 : thresholds36_138.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_138 (by decide +kernel)

theorem valid36_144 : thresholds36_144.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_144 (by decide +kernel)

theorem valid36_150 : thresholds36_150.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_150 (by decide +kernel)

theorem valid36_156 : thresholds36_156.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_156 (by decide +kernel)

theorem valid36_162 : thresholds36_162.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_162 (by decide +kernel)

theorem valid36_168 : thresholds36_168.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_168 (by decide +kernel)

theorem valid36_174 : thresholds36_174.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_174 (by decide +kernel)

theorem valid36_180 : thresholds36_180.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_180 (by decide +kernel)

theorem valid36_186 : thresholds36_186.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_186 (by decide +kernel)

theorem valid36_192 : thresholds36_192.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_192 (by decide +kernel)

theorem valid36_198 : thresholds36_198.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_198 (by decide +kernel)

theorem valid36_204 : thresholds36_204.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_204 (by decide +kernel)

theorem valid36_210 : thresholds36_210.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_210 (by decide +kernel)

theorem valid36_216 : thresholds36_216.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_216 (by decide +kernel)

theorem valid36_222 : thresholds36_222.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_222 (by decide +kernel)

theorem valid36_228 : thresholds36_228.all (checked ⟨14,7,2⟩)=true :=
  checkedVerified ⟨14,7,2⟩ prefixMap36 thresholds36_228 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand36Part001

section Pack_Z6970H2307PackedBand37Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid37_0 : thresholds37_0.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_0 (by decide +kernel)

theorem valid37_6 : thresholds37_6.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_6 (by decide +kernel)

theorem valid37_12 : thresholds37_12.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_12 (by decide +kernel)

theorem valid37_18 : thresholds37_18.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_18 (by decide +kernel)

theorem valid37_24 : thresholds37_24.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_24 (by decide +kernel)

theorem valid37_30 : thresholds37_30.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_30 (by decide +kernel)

theorem valid37_36 : thresholds37_36.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_36 (by decide +kernel)

theorem valid37_42 : thresholds37_42.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_42 (by decide +kernel)

theorem valid37_48 : thresholds37_48.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_48 (by decide +kernel)

theorem valid37_54 : thresholds37_54.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_54 (by decide +kernel)

theorem valid37_60 : thresholds37_60.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_60 (by decide +kernel)

theorem valid37_66 : thresholds37_66.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_66 (by decide +kernel)

theorem valid37_72 : thresholds37_72.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_72 (by decide +kernel)

theorem valid37_78 : thresholds37_78.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_78 (by decide +kernel)

theorem valid37_84 : thresholds37_84.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_84 (by decide +kernel)

theorem valid37_90 : thresholds37_90.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_90 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand37Part000

section Pack_Z6970H2307PackedBand37Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid37_96 : thresholds37_96.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_96 (by decide +kernel)

theorem valid37_102 : thresholds37_102.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_102 (by decide +kernel)

theorem valid37_108 : thresholds37_108.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_108 (by decide +kernel)

theorem valid37_114 : thresholds37_114.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_114 (by decide +kernel)

theorem valid37_120 : thresholds37_120.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_120 (by decide +kernel)

theorem valid37_126 : thresholds37_126.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_126 (by decide +kernel)

theorem valid37_132 : thresholds37_132.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_132 (by decide +kernel)

theorem valid37_138 : thresholds37_138.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_138 (by decide +kernel)

theorem valid37_144 : thresholds37_144.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_144 (by decide +kernel)

theorem valid37_150 : thresholds37_150.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_150 (by decide +kernel)

theorem valid37_156 : thresholds37_156.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_156 (by decide +kernel)

theorem valid37_162 : thresholds37_162.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_162 (by decide +kernel)

theorem valid37_168 : thresholds37_168.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_168 (by decide +kernel)

theorem valid37_174 : thresholds37_174.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_174 (by decide +kernel)

theorem valid37_180 : thresholds37_180.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_180 (by decide +kernel)

theorem valid37_186 : thresholds37_186.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_186 (by decide +kernel)

theorem valid37_192 : thresholds37_192.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_192 (by decide +kernel)

theorem valid37_198 : thresholds37_198.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_198 (by decide +kernel)

theorem valid37_204 : thresholds37_204.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_204 (by decide +kernel)

theorem valid37_210 : thresholds37_210.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_210 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand37Part001

section Pack_Z6970H2307PackedBand37Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid37_216 : thresholds37_216.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_216 (by decide +kernel)

theorem valid37_222 : thresholds37_222.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_222 (by decide +kernel)

theorem valid37_228 : thresholds37_228.all (checked ⟨3,8,1⟩)=true :=
  checkedVerified ⟨3,8,1⟩ prefixMap37 thresholds37_228 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand37Part002

section Pack_Z6970H2307PackedBand38Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid38_0 : thresholds38_0.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_0 (by decide +kernel)

theorem valid38_6 : thresholds38_6.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_6 (by decide +kernel)

theorem valid38_12 : thresholds38_12.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_12 (by decide +kernel)

theorem valid38_18 : thresholds38_18.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_18 (by decide +kernel)

theorem valid38_24 : thresholds38_24.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_24 (by decide +kernel)

theorem valid38_30 : thresholds38_30.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_30 (by decide +kernel)

theorem valid38_36 : thresholds38_36.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_36 (by decide +kernel)

theorem valid38_42 : thresholds38_42.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_42 (by decide +kernel)

theorem valid38_48 : thresholds38_48.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_48 (by decide +kernel)

theorem valid38_54 : thresholds38_54.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_54 (by decide +kernel)

theorem valid38_60 : thresholds38_60.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_60 (by decide +kernel)

theorem valid38_66 : thresholds38_66.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_66 (by decide +kernel)

theorem valid38_72 : thresholds38_72.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_72 (by decide +kernel)

theorem valid38_78 : thresholds38_78.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_78 (by decide +kernel)

theorem valid38_84 : thresholds38_84.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_84 (by decide +kernel)

theorem valid38_90 : thresholds38_90.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_90 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand38Part000

section Pack_Z6970H2307PackedBand38Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid38_96 : thresholds38_96.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_96 (by decide +kernel)

theorem valid38_102 : thresholds38_102.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_102 (by decide +kernel)

theorem valid38_108 : thresholds38_108.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_108 (by decide +kernel)

theorem valid38_114 : thresholds38_114.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_114 (by decide +kernel)

theorem valid38_120 : thresholds38_120.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_120 (by decide +kernel)

theorem valid38_126 : thresholds38_126.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_126 (by decide +kernel)

theorem valid38_132 : thresholds38_132.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_132 (by decide +kernel)

theorem valid38_138 : thresholds38_138.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_138 (by decide +kernel)

theorem valid38_144 : thresholds38_144.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_144 (by decide +kernel)

theorem valid38_150 : thresholds38_150.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_150 (by decide +kernel)

theorem valid38_156 : thresholds38_156.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_156 (by decide +kernel)

theorem valid38_162 : thresholds38_162.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_162 (by decide +kernel)

theorem valid38_168 : thresholds38_168.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_168 (by decide +kernel)

theorem valid38_174 : thresholds38_174.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_174 (by decide +kernel)

theorem valid38_180 : thresholds38_180.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_180 (by decide +kernel)

theorem valid38_186 : thresholds38_186.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_186 (by decide +kernel)

theorem valid38_192 : thresholds38_192.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_192 (by decide +kernel)

theorem valid38_198 : thresholds38_198.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_198 (by decide +kernel)

theorem valid38_204 : thresholds38_204.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_204 (by decide +kernel)

theorem valid38_210 : thresholds38_210.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_210 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand38Part001

section Pack_Z6970H2307PackedBand38Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid38_216 : thresholds38_216.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_216 (by decide +kernel)

theorem valid38_222 : thresholds38_222.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_222 (by decide +kernel)

theorem valid38_228 : thresholds38_228.all (checked ⟨3,8,2⟩)=true :=
  checkedVerified ⟨3,8,2⟩ prefixMap38 thresholds38_228 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand38Part002

section Pack_Z6970H2307PackedBand39Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid39_0 : thresholds39_0.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_0 (by decide +kernel)

theorem valid39_6 : thresholds39_6.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_6 (by decide +kernel)

theorem valid39_12 : thresholds39_12.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_12 (by decide +kernel)

theorem valid39_18 : thresholds39_18.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_18 (by decide +kernel)

theorem valid39_24 : thresholds39_24.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_24 (by decide +kernel)

theorem valid39_30 : thresholds39_30.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_30 (by decide +kernel)

theorem valid39_36 : thresholds39_36.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_36 (by decide +kernel)

theorem valid39_42 : thresholds39_42.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_42 (by decide +kernel)

theorem valid39_48 : thresholds39_48.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_48 (by decide +kernel)

theorem valid39_54 : thresholds39_54.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_54 (by decide +kernel)

theorem valid39_60 : thresholds39_60.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_60 (by decide +kernel)

theorem valid39_66 : thresholds39_66.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_66 (by decide +kernel)

theorem valid39_72 : thresholds39_72.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_72 (by decide +kernel)

theorem valid39_78 : thresholds39_78.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_78 (by decide +kernel)

theorem valid39_84 : thresholds39_84.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_84 (by decide +kernel)

theorem valid39_90 : thresholds39_90.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_90 (by decide +kernel)

theorem valid39_96 : thresholds39_96.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_96 (by decide +kernel)

theorem valid39_102 : thresholds39_102.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_102 (by decide +kernel)

theorem valid39_108 : thresholds39_108.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_108 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand39Part000

section Pack_Z6970H2307PackedBand39Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid39_114 : thresholds39_114.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_114 (by decide +kernel)

theorem valid39_120 : thresholds39_120.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_120 (by decide +kernel)

theorem valid39_126 : thresholds39_126.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_126 (by decide +kernel)

theorem valid39_132 : thresholds39_132.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_132 (by decide +kernel)

theorem valid39_138 : thresholds39_138.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_138 (by decide +kernel)

theorem valid39_144 : thresholds39_144.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_144 (by decide +kernel)

theorem valid39_150 : thresholds39_150.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_150 (by decide +kernel)

theorem valid39_156 : thresholds39_156.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_156 (by decide +kernel)

theorem valid39_162 : thresholds39_162.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_162 (by decide +kernel)

theorem valid39_168 : thresholds39_168.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_168 (by decide +kernel)

theorem valid39_174 : thresholds39_174.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_174 (by decide +kernel)

theorem valid39_180 : thresholds39_180.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_180 (by decide +kernel)

theorem valid39_186 : thresholds39_186.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_186 (by decide +kernel)

theorem valid39_192 : thresholds39_192.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_192 (by decide +kernel)

theorem valid39_198 : thresholds39_198.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_198 (by decide +kernel)

theorem valid39_204 : thresholds39_204.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_204 (by decide +kernel)

theorem valid39_210 : thresholds39_210.all (checked ⟨4,8,2⟩)=true :=
  checkedVerified ⟨4,8,2⟩ prefixMap39 thresholds39_210 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand39Part001

section Pack_Z6970H2307PackedBand40Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid40_0 : thresholds40_0.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_0 (by decide +kernel)

theorem valid40_6 : thresholds40_6.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_6 (by decide +kernel)

theorem valid40_12 : thresholds40_12.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_12 (by decide +kernel)

theorem valid40_18 : thresholds40_18.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_18 (by decide +kernel)

theorem valid40_24 : thresholds40_24.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_24 (by decide +kernel)

theorem valid40_30 : thresholds40_30.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_30 (by decide +kernel)

theorem valid40_36 : thresholds40_36.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_36 (by decide +kernel)

theorem valid40_42 : thresholds40_42.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_42 (by decide +kernel)

theorem valid40_48 : thresholds40_48.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_48 (by decide +kernel)

theorem valid40_54 : thresholds40_54.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_54 (by decide +kernel)

theorem valid40_60 : thresholds40_60.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_60 (by decide +kernel)

theorem valid40_66 : thresholds40_66.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_66 (by decide +kernel)

theorem valid40_72 : thresholds40_72.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_72 (by decide +kernel)

theorem valid40_78 : thresholds40_78.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_78 (by decide +kernel)

theorem valid40_84 : thresholds40_84.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_84 (by decide +kernel)

theorem valid40_90 : thresholds40_90.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_90 (by decide +kernel)

theorem valid40_96 : thresholds40_96.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_96 (by decide +kernel)

theorem valid40_102 : thresholds40_102.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_102 (by decide +kernel)

theorem valid40_108 : thresholds40_108.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_108 (by decide +kernel)

theorem valid40_114 : thresholds40_114.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_114 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand40Part000

section Pack_Z6970H2307PackedBand40Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid40_120 : thresholds40_120.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_120 (by decide +kernel)

theorem valid40_126 : thresholds40_126.all (checked ⟨7,8,1⟩)=true :=
  checkedVerified ⟨7,8,1⟩ prefixMap40 thresholds40_126 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand40Part001

section Pack_Z6970H2307PackedBand41Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid41_0 : thresholds41_0.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_0 (by decide +kernel)

theorem valid41_6 : thresholds41_6.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_6 (by decide +kernel)

theorem valid41_12 : thresholds41_12.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_12 (by decide +kernel)

theorem valid41_18 : thresholds41_18.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_18 (by decide +kernel)

theorem valid41_24 : thresholds41_24.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_24 (by decide +kernel)

theorem valid41_30 : thresholds41_30.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_30 (by decide +kernel)

theorem valid41_36 : thresholds41_36.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_36 (by decide +kernel)

theorem valid41_42 : thresholds41_42.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_42 (by decide +kernel)

theorem valid41_48 : thresholds41_48.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_48 (by decide +kernel)

theorem valid41_54 : thresholds41_54.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_54 (by decide +kernel)

theorem valid41_60 : thresholds41_60.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_60 (by decide +kernel)

theorem valid41_66 : thresholds41_66.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_66 (by decide +kernel)

theorem valid41_72 : thresholds41_72.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_72 (by decide +kernel)

theorem valid41_78 : thresholds41_78.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_78 (by decide +kernel)

theorem valid41_84 : thresholds41_84.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_84 (by decide +kernel)

theorem valid41_90 : thresholds41_90.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_90 (by decide +kernel)

theorem valid41_96 : thresholds41_96.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_96 (by decide +kernel)

theorem valid41_102 : thresholds41_102.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_102 (by decide +kernel)

theorem valid41_108 : thresholds41_108.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_108 (by decide +kernel)

theorem valid41_114 : thresholds41_114.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_114 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand41Part000

section Pack_Z6970H2307PackedBand41Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid41_120 : thresholds41_120.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_120 (by decide +kernel)

theorem valid41_126 : thresholds41_126.all (checked ⟨7,8,2⟩)=true :=
  checkedVerified ⟨7,8,2⟩ prefixMap41 thresholds41_126 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand41Part001
