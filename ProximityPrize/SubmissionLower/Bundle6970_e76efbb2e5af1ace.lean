import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_e9774b3fc07c89e3

section Pack_Z6970H2307PackedBand20Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid20_36_0 : (thresholds20_36.take 1).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_36.take 1) (by decide +kernel)

private theorem valid20_36_1 : ((thresholds20_36.drop 1).take 1).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 ((thresholds20_36.drop 1).take 1) (by decide +kernel)

private theorem valid20_36_2 : (thresholds20_36.drop 2).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_36.drop 2) (by decide +kernel)

theorem valid20_36 : thresholds20_36.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_36 1 valid20_36_0 (all_take_drop (checked ⟨2,6,1⟩) (thresholds20_36.drop 1) 1 valid20_36_1 (valid20_36_2))

private theorem valid20_42_0 : (thresholds20_42.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_42.take 4) (by decide +kernel)

private theorem valid20_42_4 : (thresholds20_42.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_42.drop 4) (by decide +kernel)

theorem valid20_42 : thresholds20_42.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_42 4 valid20_42_0 (valid20_42_4)

theorem valid20_48 : thresholds20_48.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_48 (by decide +kernel)

private theorem valid20_54_0 : (thresholds20_54.take 3).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_54.take 3) (by decide +kernel)

private theorem valid20_54_3 : ((thresholds20_54.drop 3).take 1).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 ((thresholds20_54.drop 3).take 1) (by decide +kernel)

private theorem valid20_54_4 : (thresholds20_54.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_54.drop 4) (by decide +kernel)

theorem valid20_54 : thresholds20_54.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_54 3 valid20_54_0 (all_take_drop (checked ⟨2,6,1⟩) (thresholds20_54.drop 3) 1 valid20_54_3 (valid20_54_4))

private theorem valid20_60_0 : (thresholds20_60.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_60.take 4) (by decide +kernel)

private theorem valid20_60_4 : (thresholds20_60.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_60.drop 4) (by decide +kernel)

theorem valid20_60 : thresholds20_60.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_60 4 valid20_60_0 (valid20_60_4)

theorem valid20_66 : thresholds20_66.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_66 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part001

section Pack_Z6970H2307PackedBand20Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid20_72_0 : (thresholds20_72.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_72.take 5) (by decide +kernel)

private theorem valid20_72_5 : (thresholds20_72.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_72.drop 5) (by decide +kernel)

theorem valid20_72 : thresholds20_72.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_72 5 valid20_72_0 (valid20_72_5)

private theorem valid20_78_0 : (thresholds20_78.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_78.take 4) (by decide +kernel)

private theorem valid20_78_4 : (thresholds20_78.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_78.drop 4) (by decide +kernel)

theorem valid20_78 : thresholds20_78.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_78 4 valid20_78_0 (valid20_78_4)

private theorem valid20_84_0 : (thresholds20_84.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_84.take 4) (by decide +kernel)

private theorem valid20_84_4 : (thresholds20_84.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_84.drop 4) (by decide +kernel)

theorem valid20_84 : thresholds20_84.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_84 4 valid20_84_0 (valid20_84_4)

private theorem valid20_90_0 : (thresholds20_90.take 2).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_90.take 2) (by decide +kernel)

private theorem valid20_90_2 : ((thresholds20_90.drop 2).take 3).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 ((thresholds20_90.drop 2).take 3) (by decide +kernel)

private theorem valid20_90_5 : (thresholds20_90.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_90.drop 5) (by decide +kernel)

theorem valid20_90 : thresholds20_90.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_90 2 valid20_90_0 (all_take_drop (checked ⟨2,6,1⟩) (thresholds20_90.drop 2) 3 valid20_90_2 (valid20_90_5))

private theorem valid20_96_0 : (thresholds20_96.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_96.take 5) (by decide +kernel)

private theorem valid20_96_5 : (thresholds20_96.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_96.drop 5) (by decide +kernel)

theorem valid20_96 : thresholds20_96.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_96 5 valid20_96_0 (valid20_96_5)

private theorem valid20_102_0 : (thresholds20_102.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_102.take 5) (by decide +kernel)

private theorem valid20_102_5 : (thresholds20_102.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_102.drop 5) (by decide +kernel)

theorem valid20_102 : thresholds20_102.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_102 5 valid20_102_0 (valid20_102_5)

private theorem valid20_108_0 : (thresholds20_108.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_108.take 5) (by decide +kernel)

private theorem valid20_108_5 : (thresholds20_108.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_108.drop 5) (by decide +kernel)

theorem valid20_108 : thresholds20_108.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_108 5 valid20_108_0 (valid20_108_5)

private theorem valid20_114_0 : (thresholds20_114.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_114.take 4) (by decide +kernel)

private theorem valid20_114_4 : (thresholds20_114.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_114.drop 4) (by decide +kernel)

theorem valid20_114 : thresholds20_114.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_114 4 valid20_114_0 (valid20_114_4)

private theorem valid20_120_0 : (thresholds20_120.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_120.take 4) (by decide +kernel)

private theorem valid20_120_4 : (thresholds20_120.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_120.drop 4) (by decide +kernel)

theorem valid20_120 : thresholds20_120.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_120 4 valid20_120_0 (valid20_120_4)

private theorem valid20_126_0 : (thresholds20_126.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_126.take 5) (by decide +kernel)

private theorem valid20_126_5 : (thresholds20_126.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_126.drop 5) (by decide +kernel)

theorem valid20_126 : thresholds20_126.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_126 5 valid20_126_0 (valid20_126_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part002

section Pack_Z6970H2307PackedBand20Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid20_132_0 : (thresholds20_132.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_132.take 5) (by decide +kernel)

private theorem valid20_132_5 : (thresholds20_132.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_132.drop 5) (by decide +kernel)

theorem valid20_132 : thresholds20_132.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_132 5 valid20_132_0 (valid20_132_5)

private theorem valid20_138_0 : (thresholds20_138.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_138.take 5) (by decide +kernel)

private theorem valid20_138_5 : (thresholds20_138.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_138.drop 5) (by decide +kernel)

theorem valid20_138 : thresholds20_138.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_138 5 valid20_138_0 (valid20_138_5)

private theorem valid20_144_0 : (thresholds20_144.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_144.take 5) (by decide +kernel)

private theorem valid20_144_5 : (thresholds20_144.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_144.drop 5) (by decide +kernel)

theorem valid20_144 : thresholds20_144.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_144 5 valid20_144_0 (valid20_144_5)

private theorem valid20_150_0 : (thresholds20_150.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_150.take 5) (by decide +kernel)

private theorem valid20_150_5 : (thresholds20_150.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_150.drop 5) (by decide +kernel)

theorem valid20_150 : thresholds20_150.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_150 5 valid20_150_0 (valid20_150_5)

private theorem valid20_156_0 : (thresholds20_156.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_156.take 5) (by decide +kernel)

private theorem valid20_156_5 : (thresholds20_156.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_156.drop 5) (by decide +kernel)

theorem valid20_156 : thresholds20_156.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_156 5 valid20_156_0 (valid20_156_5)

theorem valid20_162 : thresholds20_162.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_162 (by decide +kernel)

theorem valid20_168 : thresholds20_168.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_168 (by decide +kernel)

private theorem valid20_174_0 : (thresholds20_174.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_174.take 5) (by decide +kernel)

private theorem valid20_174_5 : (thresholds20_174.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_174.drop 5) (by decide +kernel)

theorem valid20_174 : thresholds20_174.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_174 5 valid20_174_0 (valid20_174_5)

theorem valid20_180 : thresholds20_180.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_180 (by decide +kernel)

private theorem valid20_186_0 : (thresholds20_186.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_186.take 5) (by decide +kernel)

private theorem valid20_186_5 : (thresholds20_186.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_186.drop 5) (by decide +kernel)

theorem valid20_186 : thresholds20_186.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_186 5 valid20_186_0 (valid20_186_5)

theorem valid20_192 : thresholds20_192.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_192 (by decide +kernel)

private theorem valid20_198_0 : (thresholds20_198.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_198.take 5) (by decide +kernel)

private theorem valid20_198_5 : (thresholds20_198.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_198.drop 5) (by decide +kernel)

theorem valid20_198 : thresholds20_198.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_198 5 valid20_198_0 (valid20_198_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part003

section Pack_Z6970H2307PackedBand20Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid20_204 : thresholds20_204.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_204 (by decide +kernel)

theorem valid20_210 : thresholds20_210.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_210 (by decide +kernel)

theorem valid20_216 : thresholds20_216.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_216 (by decide +kernel)

theorem valid20_222 : thresholds20_222.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_222 (by decide +kernel)

theorem valid20_228 : thresholds20_228.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_228 (by decide +kernel)

private theorem valid20_234_0 : (thresholds20_234.take 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_234.take 5) (by decide +kernel)

private theorem valid20_234_5 : (thresholds20_234.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_234.drop 5) (by decide +kernel)

theorem valid20_234 : thresholds20_234.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_234 5 valid20_234_0 (valid20_234_5)

theorem valid20_240 : thresholds20_240.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_240 (by decide +kernel)

theorem valid20_246 : thresholds20_246.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_246 (by decide +kernel)

theorem valid20_252 : thresholds20_252.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_252 (by decide +kernel)

theorem valid20_258 : thresholds20_258.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_258 (by decide +kernel)

theorem valid20_264 : thresholds20_264.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_264 (by decide +kernel)

theorem valid20_270 : thresholds20_270.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_270 (by decide +kernel)

theorem valid20_276 : thresholds20_276.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_276 (by decide +kernel)

theorem valid20_282 : thresholds20_282.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_282 (by decide +kernel)

theorem valid20_288 : thresholds20_288.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_288 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part004

section Pack_Z6970H2307PackedBand20Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid20_294 : thresholds20_294.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_294 (by decide +kernel)

theorem valid20_300 : thresholds20_300.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_300 (by decide +kernel)

theorem valid20_306 : thresholds20_306.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_306 (by decide +kernel)

theorem valid20_312 : thresholds20_312.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_312 (by decide +kernel)

theorem valid20_318 : thresholds20_318.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_318 (by decide +kernel)

theorem valid20_324 : thresholds20_324.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_324 (by decide +kernel)

theorem valid20_330 : thresholds20_330.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_330 (by decide +kernel)

theorem valid20_336 : thresholds20_336.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_336 (by decide +kernel)

theorem valid20_342 : thresholds20_342.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_342 (by decide +kernel)

theorem valid20_348 : thresholds20_348.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_348 (by decide +kernel)

theorem valid20_354 : thresholds20_354.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_354 (by decide +kernel)

theorem valid20_360 : thresholds20_360.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_360 (by decide +kernel)

theorem valid20_366 : thresholds20_366.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_366 (by decide +kernel)

theorem valid20_372 : thresholds20_372.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_372 (by decide +kernel)

theorem valid20_378 : thresholds20_378.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_378 (by decide +kernel)

theorem valid20_384 : thresholds20_384.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_384 (by decide +kernel)

theorem valid20_390 : thresholds20_390.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_390 (by decide +kernel)

theorem valid20_396 : thresholds20_396.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_396 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part005

section Pack_Z6970H2307PackedBand20Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid20_402 : thresholds20_402.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_402 (by decide +kernel)

theorem valid20_408 : thresholds20_408.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_408 (by decide +kernel)

theorem valid20_414 : thresholds20_414.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_414 (by decide +kernel)

theorem valid20_420 : thresholds20_420.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_420 (by decide +kernel)

theorem valid20_426 : thresholds20_426.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_426 (by decide +kernel)

theorem valid20_432 : thresholds20_432.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_432 (by decide +kernel)

theorem valid20_438 : thresholds20_438.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_438 (by decide +kernel)

theorem valid20_444 : thresholds20_444.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_444 (by decide +kernel)

theorem valid20_450 : thresholds20_450.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_450 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part006

section Pack_Z6970H2307PackedBand21Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid21_0_0 : (thresholds21_0.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_0.take 4) (by decide +kernel)

private theorem valid21_0_4 : (thresholds21_0.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_0.drop 4) (by decide +kernel)

theorem valid21_0 : thresholds21_0.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_0 4 valid21_0_0 (valid21_0_4)

theorem valid21_6 : thresholds21_6.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_6 (by decide +kernel)

theorem valid21_12 : thresholds21_12.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_12 (by decide +kernel)

theorem valid21_18 : thresholds21_18.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_18 (by decide +kernel)

private theorem valid21_24_0 : (thresholds21_24.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_24.take 4) (by decide +kernel)

private theorem valid21_24_4 : ((thresholds21_24.drop 4).take 1).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 ((thresholds21_24.drop 4).take 1) (by decide +kernel)

private theorem valid21_24_5 : (thresholds21_24.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_24.drop 5) (by decide +kernel)

theorem valid21_24 : thresholds21_24.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_24 4 valid21_24_0 (all_take_drop (checked ⟨2,6,2⟩) (thresholds21_24.drop 4) 1 valid21_24_4 (valid21_24_5))

private theorem valid21_30_0 : (thresholds21_30.take 3).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_30.take 3) (by decide +kernel)

private theorem valid21_30_3 : ((thresholds21_30.drop 3).take 2).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 ((thresholds21_30.drop 3).take 2) (by decide +kernel)

private theorem valid21_30_5 : (thresholds21_30.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_30.drop 5) (by decide +kernel)

theorem valid21_30 : thresholds21_30.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_30 3 valid21_30_0 (all_take_drop (checked ⟨2,6,2⟩) (thresholds21_30.drop 3) 2 valid21_30_3 (valid21_30_5))

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part000

section Pack_Z6970H2307PackedBand21Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid21_36_0 : (thresholds21_36.take 1).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_36.take 1) (by decide +kernel)

private theorem valid21_36_1 : ((thresholds21_36.drop 1).take 1).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 ((thresholds21_36.drop 1).take 1) (by decide +kernel)

private theorem valid21_36_2 : (thresholds21_36.drop 2).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_36.drop 2) (by decide +kernel)

theorem valid21_36 : thresholds21_36.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_36 1 valid21_36_0 (all_take_drop (checked ⟨2,6,2⟩) (thresholds21_36.drop 1) 1 valid21_36_1 (valid21_36_2))

private theorem valid21_42_0 : (thresholds21_42.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_42.take 4) (by decide +kernel)

private theorem valid21_42_4 : (thresholds21_42.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_42.drop 4) (by decide +kernel)

theorem valid21_42 : thresholds21_42.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_42 4 valid21_42_0 (valid21_42_4)

theorem valid21_48 : thresholds21_48.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_48 (by decide +kernel)

private theorem valid21_54_0 : (thresholds21_54.take 3).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_54.take 3) (by decide +kernel)

private theorem valid21_54_3 : ((thresholds21_54.drop 3).take 1).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 ((thresholds21_54.drop 3).take 1) (by decide +kernel)

private theorem valid21_54_4 : (thresholds21_54.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_54.drop 4) (by decide +kernel)

theorem valid21_54 : thresholds21_54.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_54 3 valid21_54_0 (all_take_drop (checked ⟨2,6,2⟩) (thresholds21_54.drop 3) 1 valid21_54_3 (valid21_54_4))

private theorem valid21_60_0 : (thresholds21_60.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_60.take 4) (by decide +kernel)

private theorem valid21_60_4 : (thresholds21_60.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_60.drop 4) (by decide +kernel)

theorem valid21_60 : thresholds21_60.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_60 4 valid21_60_0 (valid21_60_4)

theorem valid21_66 : thresholds21_66.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_66 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part001

section Pack_Z6970H2307PackedBand21Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid21_72_0 : (thresholds21_72.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_72.take 5) (by decide +kernel)

private theorem valid21_72_5 : (thresholds21_72.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_72.drop 5) (by decide +kernel)

theorem valid21_72 : thresholds21_72.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_72 5 valid21_72_0 (valid21_72_5)

private theorem valid21_78_0 : (thresholds21_78.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_78.take 4) (by decide +kernel)

private theorem valid21_78_4 : (thresholds21_78.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_78.drop 4) (by decide +kernel)

theorem valid21_78 : thresholds21_78.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_78 4 valid21_78_0 (valid21_78_4)

private theorem valid21_84_0 : (thresholds21_84.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_84.take 4) (by decide +kernel)

private theorem valid21_84_4 : (thresholds21_84.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_84.drop 4) (by decide +kernel)

theorem valid21_84 : thresholds21_84.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_84 4 valid21_84_0 (valid21_84_4)

private theorem valid21_90_0 : (thresholds21_90.take 2).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_90.take 2) (by decide +kernel)

private theorem valid21_90_2 : ((thresholds21_90.drop 2).take 3).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 ((thresholds21_90.drop 2).take 3) (by decide +kernel)

private theorem valid21_90_5 : (thresholds21_90.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_90.drop 5) (by decide +kernel)

theorem valid21_90 : thresholds21_90.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_90 2 valid21_90_0 (all_take_drop (checked ⟨2,6,2⟩) (thresholds21_90.drop 2) 3 valid21_90_2 (valid21_90_5))

private theorem valid21_96_0 : (thresholds21_96.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_96.take 5) (by decide +kernel)

private theorem valid21_96_5 : (thresholds21_96.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_96.drop 5) (by decide +kernel)

theorem valid21_96 : thresholds21_96.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_96 5 valid21_96_0 (valid21_96_5)

private theorem valid21_102_0 : (thresholds21_102.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_102.take 5) (by decide +kernel)

private theorem valid21_102_5 : (thresholds21_102.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_102.drop 5) (by decide +kernel)

theorem valid21_102 : thresholds21_102.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_102 5 valid21_102_0 (valid21_102_5)

private theorem valid21_108_0 : (thresholds21_108.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_108.take 5) (by decide +kernel)

private theorem valid21_108_5 : (thresholds21_108.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_108.drop 5) (by decide +kernel)

theorem valid21_108 : thresholds21_108.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_108 5 valid21_108_0 (valid21_108_5)

private theorem valid21_114_0 : (thresholds21_114.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_114.take 4) (by decide +kernel)

private theorem valid21_114_4 : (thresholds21_114.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_114.drop 4) (by decide +kernel)

theorem valid21_114 : thresholds21_114.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_114 4 valid21_114_0 (valid21_114_4)

private theorem valid21_120_0 : (thresholds21_120.take 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_120.take 4) (by decide +kernel)

private theorem valid21_120_4 : (thresholds21_120.drop 4).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_120.drop 4) (by decide +kernel)

theorem valid21_120 : thresholds21_120.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_120 4 valid21_120_0 (valid21_120_4)

private theorem valid21_126_0 : (thresholds21_126.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_126.take 5) (by decide +kernel)

private theorem valid21_126_5 : (thresholds21_126.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_126.drop 5) (by decide +kernel)

theorem valid21_126 : thresholds21_126.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_126 5 valid21_126_0 (valid21_126_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part002

section Pack_Z6970H2307PackedBand21Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid21_132_0 : (thresholds21_132.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_132.take 5) (by decide +kernel)

private theorem valid21_132_5 : (thresholds21_132.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_132.drop 5) (by decide +kernel)

theorem valid21_132 : thresholds21_132.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_132 5 valid21_132_0 (valid21_132_5)

private theorem valid21_138_0 : (thresholds21_138.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_138.take 5) (by decide +kernel)

private theorem valid21_138_5 : (thresholds21_138.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_138.drop 5) (by decide +kernel)

theorem valid21_138 : thresholds21_138.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_138 5 valid21_138_0 (valid21_138_5)

private theorem valid21_144_0 : (thresholds21_144.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_144.take 5) (by decide +kernel)

private theorem valid21_144_5 : (thresholds21_144.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_144.drop 5) (by decide +kernel)

theorem valid21_144 : thresholds21_144.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_144 5 valid21_144_0 (valid21_144_5)

private theorem valid21_150_0 : (thresholds21_150.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_150.take 5) (by decide +kernel)

private theorem valid21_150_5 : (thresholds21_150.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_150.drop 5) (by decide +kernel)

theorem valid21_150 : thresholds21_150.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_150 5 valid21_150_0 (valid21_150_5)

private theorem valid21_156_0 : (thresholds21_156.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_156.take 5) (by decide +kernel)

private theorem valid21_156_5 : (thresholds21_156.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_156.drop 5) (by decide +kernel)

theorem valid21_156 : thresholds21_156.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_156 5 valid21_156_0 (valid21_156_5)

theorem valid21_162 : thresholds21_162.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_162 (by decide +kernel)

theorem valid21_168 : thresholds21_168.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_168 (by decide +kernel)

private theorem valid21_174_0 : (thresholds21_174.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_174.take 5) (by decide +kernel)

private theorem valid21_174_5 : (thresholds21_174.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_174.drop 5) (by decide +kernel)

theorem valid21_174 : thresholds21_174.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_174 5 valid21_174_0 (valid21_174_5)

theorem valid21_180 : thresholds21_180.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_180 (by decide +kernel)

private theorem valid21_186_0 : (thresholds21_186.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_186.take 5) (by decide +kernel)

private theorem valid21_186_5 : (thresholds21_186.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_186.drop 5) (by decide +kernel)

theorem valid21_186 : thresholds21_186.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_186 5 valid21_186_0 (valid21_186_5)

theorem valid21_192 : thresholds21_192.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_192 (by decide +kernel)

private theorem valid21_198_0 : (thresholds21_198.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_198.take 5) (by decide +kernel)

private theorem valid21_198_5 : (thresholds21_198.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_198.drop 5) (by decide +kernel)

theorem valid21_198 : thresholds21_198.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_198 5 valid21_198_0 (valid21_198_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part003

section Pack_Z6970H2307PackedBand21Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid21_204 : thresholds21_204.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_204 (by decide +kernel)

theorem valid21_210 : thresholds21_210.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_210 (by decide +kernel)

theorem valid21_216 : thresholds21_216.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_216 (by decide +kernel)

theorem valid21_222 : thresholds21_222.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_222 (by decide +kernel)

theorem valid21_228 : thresholds21_228.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_228 (by decide +kernel)

private theorem valid21_234_0 : (thresholds21_234.take 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_234.take 5) (by decide +kernel)

private theorem valid21_234_5 : (thresholds21_234.drop 5).all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 (thresholds21_234.drop 5) (by decide +kernel)

theorem valid21_234 : thresholds21_234.all (checked ⟨2,6,2⟩)=true :=
  all_take_drop (checked ⟨2,6,2⟩) thresholds21_234 5 valid21_234_0 (valid21_234_5)

theorem valid21_240 : thresholds21_240.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_240 (by decide +kernel)

theorem valid21_246 : thresholds21_246.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_246 (by decide +kernel)

theorem valid21_252 : thresholds21_252.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_252 (by decide +kernel)

theorem valid21_258 : thresholds21_258.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_258 (by decide +kernel)

theorem valid21_264 : thresholds21_264.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_264 (by decide +kernel)

theorem valid21_270 : thresholds21_270.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_270 (by decide +kernel)

theorem valid21_276 : thresholds21_276.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_276 (by decide +kernel)

theorem valid21_282 : thresholds21_282.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_282 (by decide +kernel)

theorem valid21_288 : thresholds21_288.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_288 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part004

section Pack_Z6970H2307PackedBand21Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid21_294 : thresholds21_294.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_294 (by decide +kernel)

theorem valid21_300 : thresholds21_300.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_300 (by decide +kernel)

theorem valid21_306 : thresholds21_306.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_306 (by decide +kernel)

theorem valid21_312 : thresholds21_312.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_312 (by decide +kernel)

theorem valid21_318 : thresholds21_318.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_318 (by decide +kernel)

theorem valid21_324 : thresholds21_324.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_324 (by decide +kernel)

theorem valid21_330 : thresholds21_330.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_330 (by decide +kernel)

theorem valid21_336 : thresholds21_336.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_336 (by decide +kernel)

theorem valid21_342 : thresholds21_342.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_342 (by decide +kernel)

theorem valid21_348 : thresholds21_348.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_348 (by decide +kernel)

theorem valid21_354 : thresholds21_354.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_354 (by decide +kernel)

theorem valid21_360 : thresholds21_360.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_360 (by decide +kernel)

theorem valid21_366 : thresholds21_366.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_366 (by decide +kernel)

theorem valid21_372 : thresholds21_372.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_372 (by decide +kernel)

theorem valid21_378 : thresholds21_378.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_378 (by decide +kernel)

theorem valid21_384 : thresholds21_384.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_384 (by decide +kernel)

theorem valid21_390 : thresholds21_390.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_390 (by decide +kernel)

theorem valid21_396 : thresholds21_396.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_396 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part005

section Pack_Z6970H2307PackedBand21Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid21_402 : thresholds21_402.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_402 (by decide +kernel)

theorem valid21_408 : thresholds21_408.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_408 (by decide +kernel)

theorem valid21_414 : thresholds21_414.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_414 (by decide +kernel)

theorem valid21_420 : thresholds21_420.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_420 (by decide +kernel)

theorem valid21_426 : thresholds21_426.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_426 (by decide +kernel)

theorem valid21_432 : thresholds21_432.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_432 (by decide +kernel)

theorem valid21_438 : thresholds21_438.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_438 (by decide +kernel)

theorem valid21_444 : thresholds21_444.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_444 (by decide +kernel)

theorem valid21_450 : thresholds21_450.all (checked ⟨2,6,2⟩)=true :=
  checkedVerified ⟨2,6,2⟩ prefixMap21 thresholds21_450 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand21Part006

section Pack_Z6970H2307PackedBand22Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid22_0_0 : (thresholds22_0.take 3).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_0.take 3) (by decide +kernel)

private theorem valid22_0_3 : (thresholds22_0.drop 3).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_0.drop 3) (by decide +kernel)

theorem valid22_0 : thresholds22_0.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_0 3 valid22_0_0 (valid22_0_3)

theorem valid22_6 : thresholds22_6.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_6 (by decide +kernel)

theorem valid22_12 : thresholds22_12.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_12 (by decide +kernel)

theorem valid22_18 : thresholds22_18.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_18 (by decide +kernel)

theorem valid22_24 : thresholds22_24.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_24 (by decide +kernel)

theorem valid22_30 : thresholds22_30.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_30 (by decide +kernel)

theorem valid22_36 : thresholds22_36.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_36 (by decide +kernel)

private theorem valid22_42_0 : (thresholds22_42.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_42.take 5) (by decide +kernel)

private theorem valid22_42_5 : (thresholds22_42.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_42.drop 5) (by decide +kernel)

theorem valid22_42 : thresholds22_42.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_42 5 valid22_42_0 (valid22_42_5)

theorem valid22_48 : thresholds22_48.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_48 (by decide +kernel)

private theorem valid22_54_0 : (thresholds22_54.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_54.take 5) (by decide +kernel)

private theorem valid22_54_5 : (thresholds22_54.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_54.drop 5) (by decide +kernel)

theorem valid22_54 : thresholds22_54.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_54 5 valid22_54_0 (valid22_54_5)

theorem valid22_60 : thresholds22_60.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_60 (by decide +kernel)

private theorem valid22_66_0 : (thresholds22_66.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_66.take 5) (by decide +kernel)

private theorem valid22_66_5 : (thresholds22_66.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_66.drop 5) (by decide +kernel)

theorem valid22_66 : thresholds22_66.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_66 5 valid22_66_0 (valid22_66_5)

private theorem valid22_72_0 : (thresholds22_72.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_72.take 5) (by decide +kernel)

private theorem valid22_72_5 : (thresholds22_72.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_72.drop 5) (by decide +kernel)

theorem valid22_72 : thresholds22_72.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_72 5 valid22_72_0 (valid22_72_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand22Part000

section Pack_Z6970H2307PackedBand22Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid22_78_0 : (thresholds22_78.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_78.take 5) (by decide +kernel)

private theorem valid22_78_5 : (thresholds22_78.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_78.drop 5) (by decide +kernel)

theorem valid22_78 : thresholds22_78.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_78 5 valid22_78_0 (valid22_78_5)

private theorem valid22_84_0 : (thresholds22_84.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_84.take 5) (by decide +kernel)

private theorem valid22_84_5 : (thresholds22_84.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_84.drop 5) (by decide +kernel)

theorem valid22_84 : thresholds22_84.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_84 5 valid22_84_0 (valid22_84_5)

private theorem valid22_90_0 : (thresholds22_90.take 4).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_90.take 4) (by decide +kernel)

private theorem valid22_90_4 : (thresholds22_90.drop 4).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_90.drop 4) (by decide +kernel)

theorem valid22_90 : thresholds22_90.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_90 4 valid22_90_0 (valid22_90_4)

theorem valid22_96 : thresholds22_96.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_96 (by decide +kernel)

private theorem valid22_102_0 : (thresholds22_102.take 4).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_102.take 4) (by decide +kernel)

private theorem valid22_102_4 : (thresholds22_102.drop 4).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_102.drop 4) (by decide +kernel)

theorem valid22_102 : thresholds22_102.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_102 4 valid22_102_0 (valid22_102_4)

theorem valid22_108 : thresholds22_108.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_108 (by decide +kernel)

private theorem valid22_114_0 : (thresholds22_114.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_114.take 5) (by decide +kernel)

private theorem valid22_114_5 : (thresholds22_114.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_114.drop 5) (by decide +kernel)

theorem valid22_114 : thresholds22_114.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_114 5 valid22_114_0 (valid22_114_5)

theorem valid22_120 : thresholds22_120.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_120 (by decide +kernel)

theorem valid22_126 : thresholds22_126.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_126 (by decide +kernel)

theorem valid22_132 : thresholds22_132.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_132 (by decide +kernel)

private theorem valid22_138_0 : (thresholds22_138.take 4).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_138.take 4) (by decide +kernel)

private theorem valid22_138_4 : (thresholds22_138.drop 4).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_138.drop 4) (by decide +kernel)

theorem valid22_138 : thresholds22_138.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_138 4 valid22_138_0 (valid22_138_4)

theorem valid22_144 : thresholds22_144.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_144 (by decide +kernel)

theorem valid22_150 : thresholds22_150.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_150 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand22Part001

section Pack_Z6970H2307PackedBand22Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid22_156 : thresholds22_156.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_156 (by decide +kernel)

theorem valid22_162 : thresholds22_162.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_162 (by decide +kernel)

theorem valid22_168 : thresholds22_168.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_168 (by decide +kernel)

theorem valid22_174 : thresholds22_174.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_174 (by decide +kernel)

theorem valid22_180 : thresholds22_180.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_180 (by decide +kernel)

theorem valid22_186 : thresholds22_186.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_186 (by decide +kernel)

theorem valid22_192 : thresholds22_192.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_192 (by decide +kernel)

theorem valid22_198 : thresholds22_198.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_198 (by decide +kernel)

private theorem valid22_204_0 : (thresholds22_204.take 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_204.take 5) (by decide +kernel)

private theorem valid22_204_5 : (thresholds22_204.drop 5).all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 (thresholds22_204.drop 5) (by decide +kernel)

theorem valid22_204 : thresholds22_204.all (checked ⟨5,6,2⟩)=true :=
  all_take_drop (checked ⟨5,6,2⟩) thresholds22_204 5 valid22_204_0 (valid22_204_5)

theorem valid22_210 : thresholds22_210.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_210 (by decide +kernel)

theorem valid22_216 : thresholds22_216.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_216 (by decide +kernel)

theorem valid22_222 : thresholds22_222.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_222 (by decide +kernel)

theorem valid22_228 : thresholds22_228.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_228 (by decide +kernel)

theorem valid22_234 : thresholds22_234.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_234 (by decide +kernel)

theorem valid22_240 : thresholds22_240.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_240 (by decide +kernel)

theorem valid22_246 : thresholds22_246.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_246 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand22Part002

section Pack_Z6970H2307PackedBand22Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid22_252 : thresholds22_252.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_252 (by decide +kernel)

theorem valid22_258 : thresholds22_258.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_258 (by decide +kernel)

theorem valid22_264 : thresholds22_264.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_264 (by decide +kernel)

theorem valid22_270 : thresholds22_270.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_270 (by decide +kernel)

theorem valid22_276 : thresholds22_276.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_276 (by decide +kernel)

theorem valid22_282 : thresholds22_282.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_282 (by decide +kernel)

theorem valid22_288 : thresholds22_288.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_288 (by decide +kernel)

theorem valid22_294 : thresholds22_294.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_294 (by decide +kernel)

theorem valid22_300 : thresholds22_300.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_300 (by decide +kernel)

theorem valid22_306 : thresholds22_306.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_306 (by decide +kernel)

theorem valid22_312 : thresholds22_312.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_312 (by decide +kernel)

theorem valid22_318 : thresholds22_318.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_318 (by decide +kernel)

theorem valid22_324 : thresholds22_324.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_324 (by decide +kernel)

theorem valid22_330 : thresholds22_330.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_330 (by decide +kernel)

theorem valid22_336 : thresholds22_336.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_336 (by decide +kernel)

theorem valid22_342 : thresholds22_342.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_342 (by decide +kernel)

theorem valid22_348 : thresholds22_348.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_348 (by decide +kernel)

theorem valid22_354 : thresholds22_354.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_354 (by decide +kernel)

theorem valid22_360 : thresholds22_360.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_360 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand22Part003

section Pack_Z6970H2307PackedBand22Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid22_366 : thresholds22_366.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_366 (by decide +kernel)

theorem valid22_372 : thresholds22_372.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_372 (by decide +kernel)

theorem valid22_378 : thresholds22_378.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_378 (by decide +kernel)

theorem valid22_384 : thresholds22_384.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_384 (by decide +kernel)

theorem valid22_390 : thresholds22_390.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_390 (by decide +kernel)

theorem valid22_396 : thresholds22_396.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_396 (by decide +kernel)

theorem valid22_402 : thresholds22_402.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_402 (by decide +kernel)

theorem valid22_408 : thresholds22_408.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_408 (by decide +kernel)

theorem valid22_414 : thresholds22_414.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_414 (by decide +kernel)

theorem valid22_420 : thresholds22_420.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_420 (by decide +kernel)

theorem valid22_426 : thresholds22_426.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_426 (by decide +kernel)

theorem valid22_432 : thresholds22_432.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_432 (by decide +kernel)

theorem valid22_438 : thresholds22_438.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_438 (by decide +kernel)

theorem valid22_444 : thresholds22_444.all (checked ⟨5,6,2⟩)=true :=
  checkedVerified ⟨5,6,2⟩ prefixMap22 thresholds22_444 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand22Part004

section Pack_Z6970H2307PackedBand23Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid23_0_0 : (thresholds23_0.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_0.take 5) (by decide +kernel)

private theorem valid23_0_5 : (thresholds23_0.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_0.drop 5) (by decide +kernel)

theorem valid23_0 : thresholds23_0.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_0 5 valid23_0_0 (valid23_0_5)

theorem valid23_6 : thresholds23_6.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_6 (by decide +kernel)

theorem valid23_12 : thresholds23_12.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_12 (by decide +kernel)

theorem valid23_18 : thresholds23_18.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_18 (by decide +kernel)

theorem valid23_24 : thresholds23_24.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_24 (by decide +kernel)

private theorem valid23_30_0 : (thresholds23_30.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_30.take 5) (by decide +kernel)

private theorem valid23_30_5 : (thresholds23_30.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_30.drop 5) (by decide +kernel)

theorem valid23_30 : thresholds23_30.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_30 5 valid23_30_0 (valid23_30_5)

private theorem valid23_36_0 : (thresholds23_36.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_36.take 5) (by decide +kernel)

private theorem valid23_36_5 : (thresholds23_36.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_36.drop 5) (by decide +kernel)

theorem valid23_36 : thresholds23_36.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_36 5 valid23_36_0 (valid23_36_5)

theorem valid23_42 : thresholds23_42.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_42 (by decide +kernel)

theorem valid23_48 : thresholds23_48.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_48 (by decide +kernel)

theorem valid23_54 : thresholds23_54.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_54 (by decide +kernel)

private theorem valid23_60_0 : (thresholds23_60.take 4).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_60.take 4) (by decide +kernel)

private theorem valid23_60_4 : (thresholds23_60.drop 4).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_60.drop 4) (by decide +kernel)

theorem valid23_60 : thresholds23_60.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_60 4 valid23_60_0 (valid23_60_4)

theorem valid23_66 : thresholds23_66.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_66 (by decide +kernel)

private theorem valid23_72_0 : (thresholds23_72.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_72.take 5) (by decide +kernel)

private theorem valid23_72_5 : (thresholds23_72.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_72.drop 5) (by decide +kernel)

theorem valid23_72 : thresholds23_72.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_72 5 valid23_72_0 (valid23_72_5)

private theorem valid23_78_0 : (thresholds23_78.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_78.take 5) (by decide +kernel)

private theorem valid23_78_5 : (thresholds23_78.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_78.drop 5) (by decide +kernel)

theorem valid23_78 : thresholds23_78.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_78 5 valid23_78_0 (valid23_78_5)

theorem valid23_84 : thresholds23_84.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_84 (by decide +kernel)

theorem valid23_90 : thresholds23_90.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_90 (by decide +kernel)

theorem valid23_96 : thresholds23_96.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand23Part000

section Pack_Z6970H2307PackedBand23Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid23_102_0 : (thresholds23_102.take 4).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_102.take 4) (by decide +kernel)

private theorem valid23_102_4 : (thresholds23_102.drop 4).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_102.drop 4) (by decide +kernel)

theorem valid23_102 : thresholds23_102.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_102 4 valid23_102_0 (valid23_102_4)

theorem valid23_108 : thresholds23_108.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_108 (by decide +kernel)

theorem valid23_114 : thresholds23_114.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_114 (by decide +kernel)

theorem valid23_120 : thresholds23_120.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_120 (by decide +kernel)

private theorem valid23_126_0 : (thresholds23_126.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_126.take 5) (by decide +kernel)

private theorem valid23_126_5 : (thresholds23_126.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_126.drop 5) (by decide +kernel)

theorem valid23_126 : thresholds23_126.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_126 5 valid23_126_0 (valid23_126_5)

theorem valid23_132 : thresholds23_132.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_132 (by decide +kernel)

theorem valid23_138 : thresholds23_138.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_138 (by decide +kernel)

theorem valid23_144 : thresholds23_144.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_144 (by decide +kernel)

private theorem valid23_150_0 : (thresholds23_150.take 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_150.take 5) (by decide +kernel)

private theorem valid23_150_5 : (thresholds23_150.drop 5).all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 (thresholds23_150.drop 5) (by decide +kernel)

theorem valid23_150 : thresholds23_150.all (checked ⟨8,6,2⟩)=true :=
  all_take_drop (checked ⟨8,6,2⟩) thresholds23_150 5 valid23_150_0 (valid23_150_5)

theorem valid23_156 : thresholds23_156.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_156 (by decide +kernel)

theorem valid23_162 : thresholds23_162.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_162 (by decide +kernel)

theorem valid23_168 : thresholds23_168.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_168 (by decide +kernel)

theorem valid23_174 : thresholds23_174.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_174 (by decide +kernel)

theorem valid23_180 : thresholds23_180.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_180 (by decide +kernel)

theorem valid23_186 : thresholds23_186.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_186 (by decide +kernel)

theorem valid23_192 : thresholds23_192.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_192 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand23Part001

section Pack_Z6970H2307PackedBand23Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid23_198 : thresholds23_198.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_198 (by decide +kernel)

theorem valid23_204 : thresholds23_204.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_204 (by decide +kernel)

theorem valid23_210 : thresholds23_210.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_210 (by decide +kernel)

theorem valid23_216 : thresholds23_216.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_216 (by decide +kernel)

theorem valid23_222 : thresholds23_222.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_222 (by decide +kernel)

theorem valid23_228 : thresholds23_228.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_228 (by decide +kernel)

theorem valid23_234 : thresholds23_234.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_234 (by decide +kernel)

theorem valid23_240 : thresholds23_240.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_240 (by decide +kernel)

theorem valid23_246 : thresholds23_246.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_246 (by decide +kernel)

theorem valid23_252 : thresholds23_252.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_252 (by decide +kernel)

theorem valid23_258 : thresholds23_258.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_258 (by decide +kernel)

theorem valid23_264 : thresholds23_264.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_264 (by decide +kernel)

theorem valid23_270 : thresholds23_270.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_270 (by decide +kernel)

theorem valid23_276 : thresholds23_276.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_276 (by decide +kernel)

theorem valid23_282 : thresholds23_282.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_282 (by decide +kernel)

theorem valid23_288 : thresholds23_288.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_288 (by decide +kernel)

theorem valid23_294 : thresholds23_294.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_294 (by decide +kernel)

theorem valid23_300 : thresholds23_300.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_300 (by decide +kernel)

theorem valid23_306 : thresholds23_306.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_306 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand23Part002

section Pack_Z6970H2307PackedBand23Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid23_312 : thresholds23_312.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_312 (by decide +kernel)

theorem valid23_318 : thresholds23_318.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_318 (by decide +kernel)

theorem valid23_324 : thresholds23_324.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_324 (by decide +kernel)

theorem valid23_330 : thresholds23_330.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_330 (by decide +kernel)

theorem valid23_336 : thresholds23_336.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_336 (by decide +kernel)

theorem valid23_342 : thresholds23_342.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_342 (by decide +kernel)

theorem valid23_348 : thresholds23_348.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_348 (by decide +kernel)

theorem valid23_354 : thresholds23_354.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_354 (by decide +kernel)

theorem valid23_360 : thresholds23_360.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_360 (by decide +kernel)

theorem valid23_366 : thresholds23_366.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_366 (by decide +kernel)

theorem valid23_372 : thresholds23_372.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_372 (by decide +kernel)

theorem valid23_378 : thresholds23_378.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_378 (by decide +kernel)

theorem valid23_384 : thresholds23_384.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_384 (by decide +kernel)

theorem valid23_390 : thresholds23_390.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_390 (by decide +kernel)

theorem valid23_396 : thresholds23_396.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_396 (by decide +kernel)

theorem valid23_402 : thresholds23_402.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_402 (by decide +kernel)

theorem valid23_408 : thresholds23_408.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_408 (by decide +kernel)

theorem valid23_414 : thresholds23_414.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_414 (by decide +kernel)

theorem valid23_420 : thresholds23_420.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_420 (by decide +kernel)

theorem valid23_426 : thresholds23_426.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_426 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand23Part003

section Pack_Z6970H2307PackedBand23Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid23_432 : thresholds23_432.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_432 (by decide +kernel)

theorem valid23_438 : thresholds23_438.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_438 (by decide +kernel)

theorem valid23_444 : thresholds23_444.all (checked ⟨8,6,2⟩)=true :=
  checkedVerified ⟨8,6,2⟩ prefixMap23 thresholds23_444 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand23Part004

section Pack_Z6970H2307PackedBand24Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid24_0_0 : (thresholds24_0.take 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_0.take 5) (by decide +kernel)

private theorem valid24_0_5 : (thresholds24_0.drop 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_0.drop 5) (by decide +kernel)

theorem valid24_0 : thresholds24_0.all (checked ⟨11,6,2⟩)=true :=
  all_take_drop (checked ⟨11,6,2⟩) thresholds24_0 5 valid24_0_0 (valid24_0_5)

theorem valid24_6 : thresholds24_6.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_6 (by decide +kernel)

theorem valid24_12 : thresholds24_12.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_12 (by decide +kernel)

theorem valid24_18 : thresholds24_18.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_18 (by decide +kernel)

theorem valid24_24 : thresholds24_24.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_24 (by decide +kernel)

private theorem valid24_30_0 : (thresholds24_30.take 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_30.take 5) (by decide +kernel)

private theorem valid24_30_5 : (thresholds24_30.drop 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_30.drop 5) (by decide +kernel)

theorem valid24_30 : thresholds24_30.all (checked ⟨11,6,2⟩)=true :=
  all_take_drop (checked ⟨11,6,2⟩) thresholds24_30 5 valid24_30_0 (valid24_30_5)

theorem valid24_36 : thresholds24_36.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_36 (by decide +kernel)

theorem valid24_42 : thresholds24_42.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_42 (by decide +kernel)

theorem valid24_48 : thresholds24_48.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_48 (by decide +kernel)

theorem valid24_54 : thresholds24_54.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_54 (by decide +kernel)

theorem valid24_60 : thresholds24_60.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_60 (by decide +kernel)

private theorem valid24_66_0 : (thresholds24_66.take 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_66.take 5) (by decide +kernel)

private theorem valid24_66_5 : (thresholds24_66.drop 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_66.drop 5) (by decide +kernel)

theorem valid24_66 : thresholds24_66.all (checked ⟨11,6,2⟩)=true :=
  all_take_drop (checked ⟨11,6,2⟩) thresholds24_66 5 valid24_66_0 (valid24_66_5)

theorem valid24_72 : thresholds24_72.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_72 (by decide +kernel)

theorem valid24_78 : thresholds24_78.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_78 (by decide +kernel)

theorem valid24_84 : thresholds24_84.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_84 (by decide +kernel)

private theorem valid24_90_0 : (thresholds24_90.take 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_90.take 5) (by decide +kernel)

private theorem valid24_90_5 : (thresholds24_90.drop 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_90.drop 5) (by decide +kernel)

theorem valid24_90 : thresholds24_90.all (checked ⟨11,6,2⟩)=true :=
  all_take_drop (checked ⟨11,6,2⟩) thresholds24_90 5 valid24_90_0 (valid24_90_5)

theorem valid24_96 : thresholds24_96.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand24Part000

section Pack_Z6970H2307PackedBand24Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid24_102 : thresholds24_102.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_102 (by decide +kernel)

theorem valid24_108 : thresholds24_108.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_108 (by decide +kernel)

theorem valid24_114 : thresholds24_114.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_114 (by decide +kernel)

theorem valid24_120 : thresholds24_120.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_120 (by decide +kernel)

theorem valid24_126 : thresholds24_126.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_126 (by decide +kernel)

theorem valid24_132 : thresholds24_132.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_132 (by decide +kernel)

private theorem valid24_138_0 : (thresholds24_138.take 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_138.take 5) (by decide +kernel)

private theorem valid24_138_5 : (thresholds24_138.drop 5).all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 (thresholds24_138.drop 5) (by decide +kernel)

theorem valid24_138 : thresholds24_138.all (checked ⟨11,6,2⟩)=true :=
  all_take_drop (checked ⟨11,6,2⟩) thresholds24_138 5 valid24_138_0 (valid24_138_5)

theorem valid24_144 : thresholds24_144.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_144 (by decide +kernel)

theorem valid24_150 : thresholds24_150.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_150 (by decide +kernel)

theorem valid24_156 : thresholds24_156.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_156 (by decide +kernel)

theorem valid24_162 : thresholds24_162.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_162 (by decide +kernel)

theorem valid24_168 : thresholds24_168.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_168 (by decide +kernel)

theorem valid24_174 : thresholds24_174.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_174 (by decide +kernel)

theorem valid24_180 : thresholds24_180.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_180 (by decide +kernel)

theorem valid24_186 : thresholds24_186.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_186 (by decide +kernel)

theorem valid24_192 : thresholds24_192.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_192 (by decide +kernel)

theorem valid24_198 : thresholds24_198.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_198 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand24Part001

section Pack_Z6970H2307PackedBand24Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid24_204 : thresholds24_204.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_204 (by decide +kernel)

theorem valid24_210 : thresholds24_210.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_210 (by decide +kernel)

theorem valid24_216 : thresholds24_216.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_216 (by decide +kernel)

theorem valid24_222 : thresholds24_222.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_222 (by decide +kernel)

theorem valid24_228 : thresholds24_228.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_228 (by decide +kernel)

theorem valid24_234 : thresholds24_234.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_234 (by decide +kernel)

theorem valid24_240 : thresholds24_240.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_240 (by decide +kernel)

theorem valid24_246 : thresholds24_246.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_246 (by decide +kernel)

theorem valid24_252 : thresholds24_252.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_252 (by decide +kernel)

theorem valid24_258 : thresholds24_258.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_258 (by decide +kernel)

theorem valid24_264 : thresholds24_264.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_264 (by decide +kernel)

theorem valid24_270 : thresholds24_270.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_270 (by decide +kernel)

theorem valid24_276 : thresholds24_276.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_276 (by decide +kernel)

theorem valid24_282 : thresholds24_282.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_282 (by decide +kernel)

theorem valid24_288 : thresholds24_288.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_288 (by decide +kernel)

theorem valid24_294 : thresholds24_294.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_294 (by decide +kernel)

theorem valid24_300 : thresholds24_300.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_300 (by decide +kernel)

theorem valid24_306 : thresholds24_306.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_306 (by decide +kernel)

theorem valid24_312 : thresholds24_312.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_312 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand24Part002

section Pack_Z6970H2307PackedBand24Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid24_318 : thresholds24_318.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_318 (by decide +kernel)

theorem valid24_324 : thresholds24_324.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_324 (by decide +kernel)

theorem valid24_330 : thresholds24_330.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_330 (by decide +kernel)

theorem valid24_336 : thresholds24_336.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_336 (by decide +kernel)

theorem valid24_342 : thresholds24_342.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_342 (by decide +kernel)

theorem valid24_348 : thresholds24_348.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_348 (by decide +kernel)

theorem valid24_354 : thresholds24_354.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_354 (by decide +kernel)

theorem valid24_360 : thresholds24_360.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_360 (by decide +kernel)

theorem valid24_366 : thresholds24_366.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_366 (by decide +kernel)

theorem valid24_372 : thresholds24_372.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_372 (by decide +kernel)

theorem valid24_378 : thresholds24_378.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_378 (by decide +kernel)

theorem valid24_384 : thresholds24_384.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_384 (by decide +kernel)

theorem valid24_390 : thresholds24_390.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_390 (by decide +kernel)

theorem valid24_396 : thresholds24_396.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_396 (by decide +kernel)

theorem valid24_402 : thresholds24_402.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_402 (by decide +kernel)

theorem valid24_408 : thresholds24_408.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_408 (by decide +kernel)

theorem valid24_414 : thresholds24_414.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_414 (by decide +kernel)

theorem valid24_420 : thresholds24_420.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_420 (by decide +kernel)

theorem valid24_426 : thresholds24_426.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_426 (by decide +kernel)

theorem valid24_432 : thresholds24_432.all (checked ⟨11,6,2⟩)=true :=
  checkedVerified ⟨11,6,2⟩ prefixMap24 thresholds24_432 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand24Part003

section Pack_Z6970H2307PackedBand25Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid25_0_0 : (thresholds25_0.take 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_0.take 5) (by decide +kernel)

private theorem valid25_0_5 : (thresholds25_0.drop 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_0.drop 5) (by decide +kernel)

theorem valid25_0 : thresholds25_0.all (checked ⟨13,6,2⟩)=true :=
  all_take_drop (checked ⟨13,6,2⟩) thresholds25_0 5 valid25_0_0 (valid25_0_5)

theorem valid25_6 : thresholds25_6.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_6 (by decide +kernel)

theorem valid25_12 : thresholds25_12.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_12 (by decide +kernel)

theorem valid25_18 : thresholds25_18.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_18 (by decide +kernel)

private theorem valid25_24_0 : (thresholds25_24.take 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_24.take 5) (by decide +kernel)

private theorem valid25_24_5 : (thresholds25_24.drop 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_24.drop 5) (by decide +kernel)

theorem valid25_24 : thresholds25_24.all (checked ⟨13,6,2⟩)=true :=
  all_take_drop (checked ⟨13,6,2⟩) thresholds25_24 5 valid25_24_0 (valid25_24_5)

private theorem valid25_30_0 : (thresholds25_30.take 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_30.take 5) (by decide +kernel)

private theorem valid25_30_5 : (thresholds25_30.drop 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_30.drop 5) (by decide +kernel)

theorem valid25_30 : thresholds25_30.all (checked ⟨13,6,2⟩)=true :=
  all_take_drop (checked ⟨13,6,2⟩) thresholds25_30 5 valid25_30_0 (valid25_30_5)

theorem valid25_36 : thresholds25_36.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_36 (by decide +kernel)

theorem valid25_42 : thresholds25_42.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_42 (by decide +kernel)

theorem valid25_48 : thresholds25_48.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_48 (by decide +kernel)

private theorem valid25_54_0 : (thresholds25_54.take 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_54.take 5) (by decide +kernel)

private theorem valid25_54_5 : (thresholds25_54.drop 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_54.drop 5) (by decide +kernel)

theorem valid25_54 : thresholds25_54.all (checked ⟨13,6,2⟩)=true :=
  all_take_drop (checked ⟨13,6,2⟩) thresholds25_54 5 valid25_54_0 (valid25_54_5)

theorem valid25_60 : thresholds25_60.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_60 (by decide +kernel)

theorem valid25_66 : thresholds25_66.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_66 (by decide +kernel)

theorem valid25_72 : thresholds25_72.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_72 (by decide +kernel)

private theorem valid25_78_0 : (thresholds25_78.take 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_78.take 5) (by decide +kernel)

private theorem valid25_78_5 : (thresholds25_78.drop 5).all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 (thresholds25_78.drop 5) (by decide +kernel)

theorem valid25_78 : thresholds25_78.all (checked ⟨13,6,2⟩)=true :=
  all_take_drop (checked ⟨13,6,2⟩) thresholds25_78 5 valid25_78_0 (valid25_78_5)

theorem valid25_84 : thresholds25_84.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_84 (by decide +kernel)

theorem valid25_90 : thresholds25_90.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_90 (by decide +kernel)

theorem valid25_96 : thresholds25_96.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand25Part000

section Pack_Z6970H2307PackedBand25Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid25_102 : thresholds25_102.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_102 (by decide +kernel)

theorem valid25_108 : thresholds25_108.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_108 (by decide +kernel)

theorem valid25_114 : thresholds25_114.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_114 (by decide +kernel)

theorem valid25_120 : thresholds25_120.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_120 (by decide +kernel)

theorem valid25_126 : thresholds25_126.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_126 (by decide +kernel)

theorem valid25_132 : thresholds25_132.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_132 (by decide +kernel)

theorem valid25_138 : thresholds25_138.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_138 (by decide +kernel)

theorem valid25_144 : thresholds25_144.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_144 (by decide +kernel)

theorem valid25_150 : thresholds25_150.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_150 (by decide +kernel)

theorem valid25_156 : thresholds25_156.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_156 (by decide +kernel)

theorem valid25_162 : thresholds25_162.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_162 (by decide +kernel)

theorem valid25_168 : thresholds25_168.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_168 (by decide +kernel)

theorem valid25_174 : thresholds25_174.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_174 (by decide +kernel)

theorem valid25_180 : thresholds25_180.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_180 (by decide +kernel)

theorem valid25_186 : thresholds25_186.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_186 (by decide +kernel)

theorem valid25_192 : thresholds25_192.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_192 (by decide +kernel)

theorem valid25_198 : thresholds25_198.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_198 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand25Part001

section Pack_Z6970H2307PackedBand25Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid25_204 : thresholds25_204.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_204 (by decide +kernel)

theorem valid25_210 : thresholds25_210.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_210 (by decide +kernel)

theorem valid25_216 : thresholds25_216.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_216 (by decide +kernel)

theorem valid25_222 : thresholds25_222.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_222 (by decide +kernel)

theorem valid25_228 : thresholds25_228.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_228 (by decide +kernel)

theorem valid25_234 : thresholds25_234.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_234 (by decide +kernel)

theorem valid25_240 : thresholds25_240.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_240 (by decide +kernel)

theorem valid25_246 : thresholds25_246.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_246 (by decide +kernel)

theorem valid25_252 : thresholds25_252.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_252 (by decide +kernel)

theorem valid25_258 : thresholds25_258.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_258 (by decide +kernel)

theorem valid25_264 : thresholds25_264.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_264 (by decide +kernel)

theorem valid25_270 : thresholds25_270.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_270 (by decide +kernel)

theorem valid25_276 : thresholds25_276.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_276 (by decide +kernel)

theorem valid25_282 : thresholds25_282.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_282 (by decide +kernel)

theorem valid25_288 : thresholds25_288.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_288 (by decide +kernel)

theorem valid25_294 : thresholds25_294.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_294 (by decide +kernel)

theorem valid25_300 : thresholds25_300.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_300 (by decide +kernel)

theorem valid25_306 : thresholds25_306.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_306 (by decide +kernel)

theorem valid25_312 : thresholds25_312.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_312 (by decide +kernel)

theorem valid25_318 : thresholds25_318.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_318 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand25Part002

section Pack_Z6970H2307PackedBand25Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid25_324 : thresholds25_324.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_324 (by decide +kernel)

theorem valid25_330 : thresholds25_330.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_330 (by decide +kernel)

theorem valid25_336 : thresholds25_336.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_336 (by decide +kernel)

theorem valid25_342 : thresholds25_342.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_342 (by decide +kernel)

theorem valid25_348 : thresholds25_348.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_348 (by decide +kernel)

theorem valid25_354 : thresholds25_354.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_354 (by decide +kernel)

theorem valid25_360 : thresholds25_360.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_360 (by decide +kernel)

theorem valid25_366 : thresholds25_366.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_366 (by decide +kernel)

theorem valid25_372 : thresholds25_372.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_372 (by decide +kernel)

theorem valid25_378 : thresholds25_378.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_378 (by decide +kernel)

theorem valid25_384 : thresholds25_384.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_384 (by decide +kernel)

theorem valid25_390 : thresholds25_390.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_390 (by decide +kernel)

theorem valid25_396 : thresholds25_396.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_396 (by decide +kernel)

theorem valid25_402 : thresholds25_402.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_402 (by decide +kernel)

theorem valid25_408 : thresholds25_408.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_408 (by decide +kernel)

theorem valid25_414 : thresholds25_414.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_414 (by decide +kernel)

theorem valid25_420 : thresholds25_420.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_420 (by decide +kernel)

theorem valid25_426 : thresholds25_426.all (checked ⟨13,6,2⟩)=true :=
  checkedVerified ⟨13,6,2⟩ prefixMap25 thresholds25_426 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand25Part003

section Pack_Z6970H2307PackedBand26Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid26_0_0 : (thresholds26_0.take 5).all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 (thresholds26_0.take 5) (by decide +kernel)

private theorem valid26_0_5 : (thresholds26_0.drop 5).all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 (thresholds26_0.drop 5) (by decide +kernel)

theorem valid26_0 : thresholds26_0.all (checked ⟨15,6,2⟩)=true :=
  all_take_drop (checked ⟨15,6,2⟩) thresholds26_0 5 valid26_0_0 (valid26_0_5)

theorem valid26_6 : thresholds26_6.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_6 (by decide +kernel)

theorem valid26_12 : thresholds26_12.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_12 (by decide +kernel)

theorem valid26_18 : thresholds26_18.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_18 (by decide +kernel)

theorem valid26_24 : thresholds26_24.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_24 (by decide +kernel)

theorem valid26_30 : thresholds26_30.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_30 (by decide +kernel)

private theorem valid26_36_0 : (thresholds26_36.take 5).all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 (thresholds26_36.take 5) (by decide +kernel)

private theorem valid26_36_5 : (thresholds26_36.drop 5).all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 (thresholds26_36.drop 5) (by decide +kernel)

theorem valid26_36 : thresholds26_36.all (checked ⟨15,6,2⟩)=true :=
  all_take_drop (checked ⟨15,6,2⟩) thresholds26_36 5 valid26_36_0 (valid26_36_5)

theorem valid26_42 : thresholds26_42.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_42 (by decide +kernel)

theorem valid26_48 : thresholds26_48.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_48 (by decide +kernel)

theorem valid26_54 : thresholds26_54.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_54 (by decide +kernel)

theorem valid26_60 : thresholds26_60.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_60 (by decide +kernel)

theorem valid26_66 : thresholds26_66.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_66 (by decide +kernel)

theorem valid26_72 : thresholds26_72.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_72 (by decide +kernel)

theorem valid26_78 : thresholds26_78.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_78 (by decide +kernel)

theorem valid26_84 : thresholds26_84.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_84 (by decide +kernel)

theorem valid26_90 : thresholds26_90.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_90 (by decide +kernel)

theorem valid26_96 : thresholds26_96.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand26Part000

section Pack_Z6970H2307PackedBand26Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid26_102 : thresholds26_102.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_102 (by decide +kernel)

theorem valid26_108 : thresholds26_108.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_108 (by decide +kernel)

theorem valid26_114 : thresholds26_114.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_114 (by decide +kernel)

theorem valid26_120 : thresholds26_120.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_120 (by decide +kernel)

theorem valid26_126 : thresholds26_126.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_126 (by decide +kernel)

theorem valid26_132 : thresholds26_132.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_132 (by decide +kernel)

theorem valid26_138 : thresholds26_138.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_138 (by decide +kernel)

theorem valid26_144 : thresholds26_144.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_144 (by decide +kernel)

theorem valid26_150 : thresholds26_150.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_150 (by decide +kernel)

theorem valid26_156 : thresholds26_156.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_156 (by decide +kernel)

theorem valid26_162 : thresholds26_162.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_162 (by decide +kernel)

theorem valid26_168 : thresholds26_168.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_168 (by decide +kernel)

theorem valid26_174 : thresholds26_174.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_174 (by decide +kernel)

theorem valid26_180 : thresholds26_180.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_180 (by decide +kernel)

theorem valid26_186 : thresholds26_186.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_186 (by decide +kernel)

theorem valid26_192 : thresholds26_192.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_192 (by decide +kernel)

theorem valid26_198 : thresholds26_198.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_198 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand26Part001

section Pack_Z6970H2307PackedBand26Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid26_204 : thresholds26_204.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_204 (by decide +kernel)

theorem valid26_210 : thresholds26_210.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_210 (by decide +kernel)

theorem valid26_216 : thresholds26_216.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_216 (by decide +kernel)

theorem valid26_222 : thresholds26_222.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_222 (by decide +kernel)

theorem valid26_228 : thresholds26_228.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_228 (by decide +kernel)

theorem valid26_234 : thresholds26_234.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_234 (by decide +kernel)

theorem valid26_240 : thresholds26_240.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_240 (by decide +kernel)

theorem valid26_246 : thresholds26_246.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_246 (by decide +kernel)

theorem valid26_252 : thresholds26_252.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_252 (by decide +kernel)

theorem valid26_258 : thresholds26_258.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_258 (by decide +kernel)

theorem valid26_264 : thresholds26_264.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_264 (by decide +kernel)

theorem valid26_270 : thresholds26_270.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_270 (by decide +kernel)

theorem valid26_276 : thresholds26_276.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_276 (by decide +kernel)

theorem valid26_282 : thresholds26_282.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_282 (by decide +kernel)

theorem valid26_288 : thresholds26_288.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_288 (by decide +kernel)

theorem valid26_294 : thresholds26_294.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_294 (by decide +kernel)

theorem valid26_300 : thresholds26_300.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_300 (by decide +kernel)

theorem valid26_306 : thresholds26_306.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_306 (by decide +kernel)

theorem valid26_312 : thresholds26_312.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_312 (by decide +kernel)

theorem valid26_318 : thresholds26_318.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_318 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand26Part002

section Pack_Z6970H2307PackedBand26Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid26_324 : thresholds26_324.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_324 (by decide +kernel)

theorem valid26_330 : thresholds26_330.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_330 (by decide +kernel)

theorem valid26_336 : thresholds26_336.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_336 (by decide +kernel)

theorem valid26_342 : thresholds26_342.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_342 (by decide +kernel)

theorem valid26_348 : thresholds26_348.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_348 (by decide +kernel)

theorem valid26_354 : thresholds26_354.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_354 (by decide +kernel)

theorem valid26_360 : thresholds26_360.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_360 (by decide +kernel)

theorem valid26_366 : thresholds26_366.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_366 (by decide +kernel)

theorem valid26_372 : thresholds26_372.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_372 (by decide +kernel)

theorem valid26_378 : thresholds26_378.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_378 (by decide +kernel)

theorem valid26_384 : thresholds26_384.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_384 (by decide +kernel)

theorem valid26_390 : thresholds26_390.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_390 (by decide +kernel)

theorem valid26_396 : thresholds26_396.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_396 (by decide +kernel)

theorem valid26_402 : thresholds26_402.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_402 (by decide +kernel)

theorem valid26_408 : thresholds26_408.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_408 (by decide +kernel)

theorem valid26_414 : thresholds26_414.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_414 (by decide +kernel)

theorem valid26_420 : thresholds26_420.all (checked ⟨15,6,2⟩)=true :=
  checkedVerified ⟨15,6,2⟩ prefixMap26 thresholds26_420 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand26Part003

section Pack_Z6970H2307PackedBand27Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid27_0_0 : (thresholds27_0.take 5).all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 (thresholds27_0.take 5) (by decide +kernel)

private theorem valid27_0_5 : (thresholds27_0.drop 5).all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 (thresholds27_0.drop 5) (by decide +kernel)

theorem valid27_0 : thresholds27_0.all (checked ⟨17,6,2⟩)=true :=
  all_take_drop (checked ⟨17,6,2⟩) thresholds27_0 5 valid27_0_0 (valid27_0_5)

theorem valid27_6 : thresholds27_6.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_6 (by decide +kernel)

theorem valid27_12 : thresholds27_12.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_12 (by decide +kernel)

theorem valid27_18 : thresholds27_18.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_18 (by decide +kernel)

private theorem valid27_24_0 : (thresholds27_24.take 5).all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 (thresholds27_24.take 5) (by decide +kernel)

private theorem valid27_24_5 : (thresholds27_24.drop 5).all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 (thresholds27_24.drop 5) (by decide +kernel)

theorem valid27_24 : thresholds27_24.all (checked ⟨17,6,2⟩)=true :=
  all_take_drop (checked ⟨17,6,2⟩) thresholds27_24 5 valid27_24_0 (valid27_24_5)

theorem valid27_30 : thresholds27_30.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_30 (by decide +kernel)

theorem valid27_36 : thresholds27_36.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_36 (by decide +kernel)

theorem valid27_42 : thresholds27_42.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_42 (by decide +kernel)

theorem valid27_48 : thresholds27_48.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_48 (by decide +kernel)

theorem valid27_54 : thresholds27_54.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_54 (by decide +kernel)

theorem valid27_60 : thresholds27_60.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_60 (by decide +kernel)

theorem valid27_66 : thresholds27_66.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_66 (by decide +kernel)

theorem valid27_72 : thresholds27_72.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_72 (by decide +kernel)

theorem valid27_78 : thresholds27_78.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_78 (by decide +kernel)

theorem valid27_84 : thresholds27_84.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_84 (by decide +kernel)

theorem valid27_90 : thresholds27_90.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_90 (by decide +kernel)

theorem valid27_96 : thresholds27_96.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand27Part000

section Pack_Z6970H2307PackedBand27Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid27_102 : thresholds27_102.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_102 (by decide +kernel)

theorem valid27_108 : thresholds27_108.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_108 (by decide +kernel)

theorem valid27_114 : thresholds27_114.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_114 (by decide +kernel)

theorem valid27_120 : thresholds27_120.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_120 (by decide +kernel)

theorem valid27_126 : thresholds27_126.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_126 (by decide +kernel)

theorem valid27_132 : thresholds27_132.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_132 (by decide +kernel)

theorem valid27_138 : thresholds27_138.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_138 (by decide +kernel)

theorem valid27_144 : thresholds27_144.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_144 (by decide +kernel)

theorem valid27_150 : thresholds27_150.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_150 (by decide +kernel)

theorem valid27_156 : thresholds27_156.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_156 (by decide +kernel)

theorem valid27_162 : thresholds27_162.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_162 (by decide +kernel)

theorem valid27_168 : thresholds27_168.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_168 (by decide +kernel)

theorem valid27_174 : thresholds27_174.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_174 (by decide +kernel)

theorem valid27_180 : thresholds27_180.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_180 (by decide +kernel)

theorem valid27_186 : thresholds27_186.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_186 (by decide +kernel)

theorem valid27_192 : thresholds27_192.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_192 (by decide +kernel)

theorem valid27_198 : thresholds27_198.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_198 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand27Part001

section Pack_Z6970H2307PackedBand27Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid27_204 : thresholds27_204.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_204 (by decide +kernel)

theorem valid27_210 : thresholds27_210.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_210 (by decide +kernel)

theorem valid27_216 : thresholds27_216.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_216 (by decide +kernel)

theorem valid27_222 : thresholds27_222.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_222 (by decide +kernel)

theorem valid27_228 : thresholds27_228.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_228 (by decide +kernel)

theorem valid27_234 : thresholds27_234.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_234 (by decide +kernel)

theorem valid27_240 : thresholds27_240.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_240 (by decide +kernel)

theorem valid27_246 : thresholds27_246.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_246 (by decide +kernel)

theorem valid27_252 : thresholds27_252.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_252 (by decide +kernel)

theorem valid27_258 : thresholds27_258.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_258 (by decide +kernel)

theorem valid27_264 : thresholds27_264.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_264 (by decide +kernel)

theorem valid27_270 : thresholds27_270.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_270 (by decide +kernel)

theorem valid27_276 : thresholds27_276.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_276 (by decide +kernel)

theorem valid27_282 : thresholds27_282.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_282 (by decide +kernel)

theorem valid27_288 : thresholds27_288.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_288 (by decide +kernel)

theorem valid27_294 : thresholds27_294.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_294 (by decide +kernel)

theorem valid27_300 : thresholds27_300.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_300 (by decide +kernel)

theorem valid27_306 : thresholds27_306.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_306 (by decide +kernel)

theorem valid27_312 : thresholds27_312.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_312 (by decide +kernel)

theorem valid27_318 : thresholds27_318.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_318 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand27Part002

section Pack_Z6970H2307PackedBand27Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid27_324 : thresholds27_324.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_324 (by decide +kernel)

theorem valid27_330 : thresholds27_330.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_330 (by decide +kernel)

theorem valid27_336 : thresholds27_336.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_336 (by decide +kernel)

theorem valid27_342 : thresholds27_342.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_342 (by decide +kernel)

theorem valid27_348 : thresholds27_348.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_348 (by decide +kernel)

theorem valid27_354 : thresholds27_354.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_354 (by decide +kernel)

theorem valid27_360 : thresholds27_360.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_360 (by decide +kernel)

theorem valid27_366 : thresholds27_366.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_366 (by decide +kernel)

theorem valid27_372 : thresholds27_372.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_372 (by decide +kernel)

theorem valid27_378 : thresholds27_378.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_378 (by decide +kernel)

theorem valid27_384 : thresholds27_384.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_384 (by decide +kernel)

theorem valid27_390 : thresholds27_390.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_390 (by decide +kernel)

theorem valid27_396 : thresholds27_396.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_396 (by decide +kernel)

theorem valid27_402 : thresholds27_402.all (checked ⟨17,6,2⟩)=true :=
  checkedVerified ⟨17,6,2⟩ prefixMap27 thresholds27_402 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand27Part003

section Pack_Z6970H2307PackedBand28Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid28_0 : thresholds28_0.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_0 (by decide +kernel)

theorem valid28_6 : thresholds28_6.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_6 (by decide +kernel)

theorem valid28_12 : thresholds28_12.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_12 (by decide +kernel)

theorem valid28_18 : thresholds28_18.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_18 (by decide +kernel)

theorem valid28_24 : thresholds28_24.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_24 (by decide +kernel)

theorem valid28_30 : thresholds28_30.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_30 (by decide +kernel)

theorem valid28_36 : thresholds28_36.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_36 (by decide +kernel)

theorem valid28_42 : thresholds28_42.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_42 (by decide +kernel)

theorem valid28_48 : thresholds28_48.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_48 (by decide +kernel)

theorem valid28_54 : thresholds28_54.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_54 (by decide +kernel)

theorem valid28_60 : thresholds28_60.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_60 (by decide +kernel)

theorem valid28_66 : thresholds28_66.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_66 (by decide +kernel)

theorem valid28_72 : thresholds28_72.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_72 (by decide +kernel)

theorem valid28_78 : thresholds28_78.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_78 (by decide +kernel)

theorem valid28_84 : thresholds28_84.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_84 (by decide +kernel)

theorem valid28_90 : thresholds28_90.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_90 (by decide +kernel)

theorem valid28_96 : thresholds28_96.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_96 (by decide +kernel)

theorem valid28_102 : thresholds28_102.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_102 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand28Part000

section Pack_Z6970H2307PackedBand28Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid28_108 : thresholds28_108.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_108 (by decide +kernel)

theorem valid28_114 : thresholds28_114.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_114 (by decide +kernel)

theorem valid28_120 : thresholds28_120.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_120 (by decide +kernel)

theorem valid28_126 : thresholds28_126.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_126 (by decide +kernel)

theorem valid28_132 : thresholds28_132.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_132 (by decide +kernel)

theorem valid28_138 : thresholds28_138.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_138 (by decide +kernel)

theorem valid28_144 : thresholds28_144.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_144 (by decide +kernel)

theorem valid28_150 : thresholds28_150.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_150 (by decide +kernel)

theorem valid28_156 : thresholds28_156.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_156 (by decide +kernel)

theorem valid28_162 : thresholds28_162.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_162 (by decide +kernel)

theorem valid28_168 : thresholds28_168.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_168 (by decide +kernel)

theorem valid28_174 : thresholds28_174.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_174 (by decide +kernel)

theorem valid28_180 : thresholds28_180.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_180 (by decide +kernel)

theorem valid28_186 : thresholds28_186.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_186 (by decide +kernel)

theorem valid28_192 : thresholds28_192.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_192 (by decide +kernel)

theorem valid28_198 : thresholds28_198.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_198 (by decide +kernel)

theorem valid28_204 : thresholds28_204.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_204 (by decide +kernel)

theorem valid28_210 : thresholds28_210.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_210 (by decide +kernel)

theorem valid28_216 : thresholds28_216.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_216 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand28Part001

section Pack_Z6970H2307PackedBand28Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid28_222 : thresholds28_222.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_222 (by decide +kernel)

theorem valid28_228 : thresholds28_228.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_228 (by decide +kernel)

theorem valid28_234 : thresholds28_234.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_234 (by decide +kernel)

theorem valid28_240 : thresholds28_240.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_240 (by decide +kernel)

theorem valid28_246 : thresholds28_246.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_246 (by decide +kernel)

theorem valid28_252 : thresholds28_252.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_252 (by decide +kernel)

theorem valid28_258 : thresholds28_258.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_258 (by decide +kernel)

theorem valid28_264 : thresholds28_264.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_264 (by decide +kernel)

theorem valid28_270 : thresholds28_270.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_270 (by decide +kernel)

theorem valid28_276 : thresholds28_276.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_276 (by decide +kernel)

theorem valid28_282 : thresholds28_282.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_282 (by decide +kernel)

theorem valid28_288 : thresholds28_288.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_288 (by decide +kernel)

theorem valid28_294 : thresholds28_294.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_294 (by decide +kernel)

theorem valid28_300 : thresholds28_300.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_300 (by decide +kernel)

theorem valid28_306 : thresholds28_306.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_306 (by decide +kernel)

theorem valid28_312 : thresholds28_312.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_312 (by decide +kernel)

theorem valid28_318 : thresholds28_318.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_318 (by decide +kernel)

theorem valid28_324 : thresholds28_324.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_324 (by decide +kernel)

theorem valid28_330 : thresholds28_330.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_330 (by decide +kernel)

theorem valid28_336 : thresholds28_336.all (checked ⟨19,6,2⟩)=true :=
  checkedVerified ⟨19,6,2⟩ prefixMap28 thresholds28_336 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand28Part002
