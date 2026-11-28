import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_e9774b3fc07c89e3

section Pack_Z6970H2307PackedBand14Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid14_0_0 : (thresholds14_0.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_0.take 4) (by decide +kernel)

private theorem valid14_0_4 : (thresholds14_0.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_0.drop 4) (by decide +kernel)

theorem valid14_0 : thresholds14_0.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_0 4 valid14_0_0 (valid14_0_4)

theorem valid14_6 : thresholds14_6.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_6 (by decide +kernel)

theorem valid14_12 : thresholds14_12.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_12 (by decide +kernel)

theorem valid14_18 : thresholds14_18.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_18 (by decide +kernel)

theorem valid14_24 : thresholds14_24.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_24 (by decide +kernel)

private theorem valid14_30_0 : (thresholds14_30.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_30.take 4) (by decide +kernel)

private theorem valid14_30_4 : (thresholds14_30.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_30.drop 4) (by decide +kernel)

theorem valid14_30 : thresholds14_30.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_30 4 valid14_30_0 (valid14_30_4)

private theorem valid14_36_0 : (thresholds14_36.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_36.take 5) (by decide +kernel)

private theorem valid14_36_5 : (thresholds14_36.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_36.drop 5) (by decide +kernel)

theorem valid14_36 : thresholds14_36.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_36 5 valid14_36_0 (valid14_36_5)

private theorem valid14_42_0 : (thresholds14_42.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_42.take 5) (by decide +kernel)

private theorem valid14_42_5 : (thresholds14_42.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_42.drop 5) (by decide +kernel)

theorem valid14_42 : thresholds14_42.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_42 5 valid14_42_0 (valid14_42_5)

theorem valid14_48 : thresholds14_48.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_48 (by decide +kernel)

private theorem valid14_54_0 : (thresholds14_54.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_54.take 5) (by decide +kernel)

private theorem valid14_54_5 : (thresholds14_54.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_54.drop 5) (by decide +kernel)

theorem valid14_54 : thresholds14_54.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_54 5 valid14_54_0 (valid14_54_5)

private theorem valid14_60_0 : (thresholds14_60.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_60.take 5) (by decide +kernel)

private theorem valid14_60_5 : (thresholds14_60.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_60.drop 5) (by decide +kernel)

theorem valid14_60 : thresholds14_60.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_60 5 valid14_60_0 (valid14_60_5)

theorem valid14_66 : thresholds14_66.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_66 (by decide +kernel)

private theorem valid14_72_0 : (thresholds14_72.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_72.take 4) (by decide +kernel)

private theorem valid14_72_4 : (thresholds14_72.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_72.drop 4) (by decide +kernel)

theorem valid14_72 : thresholds14_72.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_72 4 valid14_72_0 (valid14_72_4)

private theorem valid14_78_0 : (thresholds14_78.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_78.take 5) (by decide +kernel)

private theorem valid14_78_5 : (thresholds14_78.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_78.drop 5) (by decide +kernel)

theorem valid14_78 : thresholds14_78.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_78 5 valid14_78_0 (valid14_78_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part000

section Pack_Z6970H2307PackedBand14Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid14_84_0 : (thresholds14_84.take 3).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_84.take 3) (by decide +kernel)

private theorem valid14_84_3 : (thresholds14_84.drop 3).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_84.drop 3) (by decide +kernel)

theorem valid14_84 : thresholds14_84.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_84 3 valid14_84_0 (valid14_84_3)

private theorem valid14_90_0 : (thresholds14_90.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_90.take 4) (by decide +kernel)

private theorem valid14_90_4 : (thresholds14_90.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_90.drop 4) (by decide +kernel)

theorem valid14_90 : thresholds14_90.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_90 4 valid14_90_0 (valid14_90_4)

private theorem valid14_96_0 : (thresholds14_96.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_96.take 5) (by decide +kernel)

private theorem valid14_96_5 : (thresholds14_96.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_96.drop 5) (by decide +kernel)

theorem valid14_96 : thresholds14_96.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_96 5 valid14_96_0 (valid14_96_5)

private theorem valid14_102_0 : (thresholds14_102.take 3).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_102.take 3) (by decide +kernel)

private theorem valid14_102_3 : (thresholds14_102.drop 3).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_102.drop 3) (by decide +kernel)

theorem valid14_102 : thresholds14_102.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_102 3 valid14_102_0 (valid14_102_3)

private theorem valid14_108_0 : (thresholds14_108.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_108.take 4) (by decide +kernel)

private theorem valid14_108_4 : (thresholds14_108.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_108.drop 4) (by decide +kernel)

theorem valid14_108 : thresholds14_108.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_108 4 valid14_108_0 (valid14_108_4)

theorem valid14_114 : thresholds14_114.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_114 (by decide +kernel)

private theorem valid14_120_0 : (thresholds14_120.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_120.take 4) (by decide +kernel)

private theorem valid14_120_4 : (thresholds14_120.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_120.drop 4) (by decide +kernel)

theorem valid14_120 : thresholds14_120.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_120 4 valid14_120_0 (valid14_120_4)

theorem valid14_126 : thresholds14_126.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_126 (by decide +kernel)

private theorem valid14_132_0 : (thresholds14_132.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_132.take 5) (by decide +kernel)

private theorem valid14_132_5 : (thresholds14_132.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_132.drop 5) (by decide +kernel)

theorem valid14_132 : thresholds14_132.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_132 5 valid14_132_0 (valid14_132_5)

private theorem valid14_138_0 : (thresholds14_138.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_138.take 5) (by decide +kernel)

private theorem valid14_138_5 : (thresholds14_138.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_138.drop 5) (by decide +kernel)

theorem valid14_138 : thresholds14_138.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_138 5 valid14_138_0 (valid14_138_5)

private theorem valid14_144_0 : (thresholds14_144.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_144.take 5) (by decide +kernel)

private theorem valid14_144_5 : (thresholds14_144.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_144.drop 5) (by decide +kernel)

theorem valid14_144 : thresholds14_144.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_144 5 valid14_144_0 (valid14_144_5)

private theorem valid14_150_0 : (thresholds14_150.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_150.take 4) (by decide +kernel)

private theorem valid14_150_4 : (thresholds14_150.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_150.drop 4) (by decide +kernel)

theorem valid14_150 : thresholds14_150.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_150 4 valid14_150_0 (valid14_150_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part001

section Pack_Z6970H2307PackedBand14Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid14_156_0 : (thresholds14_156.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_156.take 4) (by decide +kernel)

private theorem valid14_156_4 : (thresholds14_156.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_156.drop 4) (by decide +kernel)

theorem valid14_156 : thresholds14_156.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_156 4 valid14_156_0 (valid14_156_4)

private theorem valid14_162_0 : (thresholds14_162.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_162.take 4) (by decide +kernel)

private theorem valid14_162_4 : (thresholds14_162.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_162.drop 4) (by decide +kernel)

theorem valid14_162 : thresholds14_162.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_162 4 valid14_162_0 (valid14_162_4)

private theorem valid14_168_0 : (thresholds14_168.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_168.take 4) (by decide +kernel)

private theorem valid14_168_4 : (thresholds14_168.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_168.drop 4) (by decide +kernel)

theorem valid14_168 : thresholds14_168.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_168 4 valid14_168_0 (valid14_168_4)

private theorem valid14_174_0 : (thresholds14_174.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_174.take 5) (by decide +kernel)

private theorem valid14_174_5 : (thresholds14_174.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_174.drop 5) (by decide +kernel)

theorem valid14_174 : thresholds14_174.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_174 5 valid14_174_0 (valid14_174_5)

theorem valid14_180 : thresholds14_180.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_180 (by decide +kernel)

private theorem valid14_186_0 : (thresholds14_186.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_186.take 5) (by decide +kernel)

private theorem valid14_186_5 : (thresholds14_186.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_186.drop 5) (by decide +kernel)

theorem valid14_186 : thresholds14_186.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_186 5 valid14_186_0 (valid14_186_5)

theorem valid14_192 : thresholds14_192.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_192 (by decide +kernel)

private theorem valid14_198_0 : (thresholds14_198.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_198.take 5) (by decide +kernel)

private theorem valid14_198_5 : (thresholds14_198.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_198.drop 5) (by decide +kernel)

theorem valid14_198 : thresholds14_198.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_198 5 valid14_198_0 (valid14_198_5)

theorem valid14_204 : thresholds14_204.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_204 (by decide +kernel)

private theorem valid14_210_0 : (thresholds14_210.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_210.take 4) (by decide +kernel)

private theorem valid14_210_4 : (thresholds14_210.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_210.drop 4) (by decide +kernel)

theorem valid14_210 : thresholds14_210.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_210 4 valid14_210_0 (valid14_210_4)

private theorem valid14_216_0 : (thresholds14_216.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_216.take 5) (by decide +kernel)

private theorem valid14_216_5 : (thresholds14_216.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_216.drop 5) (by decide +kernel)

theorem valid14_216 : thresholds14_216.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_216 5 valid14_216_0 (valid14_216_5)

private theorem valid14_222_0 : (thresholds14_222.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_222.take 5) (by decide +kernel)

private theorem valid14_222_5 : (thresholds14_222.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_222.drop 5) (by decide +kernel)

theorem valid14_222 : thresholds14_222.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_222 5 valid14_222_0 (valid14_222_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part002

section Pack_Z6970H2307PackedBand14Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid14_228_0 : (thresholds14_228.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_228.take 4) (by decide +kernel)

private theorem valid14_228_4 : (thresholds14_228.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_228.drop 4) (by decide +kernel)

theorem valid14_228 : thresholds14_228.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_228 4 valid14_228_0 (valid14_228_4)

private theorem valid14_234_0 : (thresholds14_234.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_234.take 5) (by decide +kernel)

private theorem valid14_234_5 : (thresholds14_234.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_234.drop 5) (by decide +kernel)

theorem valid14_234 : thresholds14_234.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_234 5 valid14_234_0 (valid14_234_5)

theorem valid14_240 : thresholds14_240.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_240 (by decide +kernel)

theorem valid14_246 : thresholds14_246.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_246 (by decide +kernel)

theorem valid14_252 : thresholds14_252.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_252 (by decide +kernel)

private theorem valid14_258_0 : (thresholds14_258.take 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_258.take 4) (by decide +kernel)

private theorem valid14_258_4 : (thresholds14_258.drop 4).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_258.drop 4) (by decide +kernel)

theorem valid14_258 : thresholds14_258.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_258 4 valid14_258_0 (valid14_258_4)

theorem valid14_264 : thresholds14_264.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_264 (by decide +kernel)

private theorem valid14_270_0 : (thresholds14_270.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_270.take 5) (by decide +kernel)

private theorem valid14_270_5 : (thresholds14_270.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_270.drop 5) (by decide +kernel)

theorem valid14_270 : thresholds14_270.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_270 5 valid14_270_0 (valid14_270_5)

private theorem valid14_276_0 : (thresholds14_276.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_276.take 5) (by decide +kernel)

private theorem valid14_276_5 : (thresholds14_276.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_276.drop 5) (by decide +kernel)

theorem valid14_276 : thresholds14_276.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_276 5 valid14_276_0 (valid14_276_5)

private theorem valid14_282_0 : (thresholds14_282.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_282.take 5) (by decide +kernel)

private theorem valid14_282_5 : (thresholds14_282.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_282.drop 5) (by decide +kernel)

theorem valid14_282 : thresholds14_282.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_282 5 valid14_282_0 (valid14_282_5)

theorem valid14_288 : thresholds14_288.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_288 (by decide +kernel)

private theorem valid14_294_0 : (thresholds14_294.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_294.take 5) (by decide +kernel)

private theorem valid14_294_5 : (thresholds14_294.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_294.drop 5) (by decide +kernel)

theorem valid14_294 : thresholds14_294.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_294 5 valid14_294_0 (valid14_294_5)

theorem valid14_300 : thresholds14_300.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_300 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part003

section Pack_Z6970H2307PackedBand14Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid14_306 : thresholds14_306.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_306 (by decide +kernel)

theorem valid14_312 : thresholds14_312.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_312 (by decide +kernel)

theorem valid14_318 : thresholds14_318.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_318 (by decide +kernel)

private theorem valid14_324_0 : (thresholds14_324.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_324.take 5) (by decide +kernel)

private theorem valid14_324_5 : (thresholds14_324.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_324.drop 5) (by decide +kernel)

theorem valid14_324 : thresholds14_324.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_324 5 valid14_324_0 (valid14_324_5)

theorem valid14_330 : thresholds14_330.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_330 (by decide +kernel)

private theorem valid14_336_0 : (thresholds14_336.take 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_336.take 5) (by decide +kernel)

private theorem valid14_336_5 : (thresholds14_336.drop 5).all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 (thresholds14_336.drop 5) (by decide +kernel)

theorem valid14_336 : thresholds14_336.all (checked ⟨10,3,1⟩)=true :=
  all_take_drop (checked ⟨10,3,1⟩) thresholds14_336 5 valid14_336_0 (valid14_336_5)

theorem valid14_342 : thresholds14_342.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_342 (by decide +kernel)

theorem valid14_348 : thresholds14_348.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_348 (by decide +kernel)

theorem valid14_354 : thresholds14_354.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_354 (by decide +kernel)

theorem valid14_360 : thresholds14_360.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_360 (by decide +kernel)

theorem valid14_366 : thresholds14_366.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_366 (by decide +kernel)

theorem valid14_372 : thresholds14_372.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_372 (by decide +kernel)

theorem valid14_378 : thresholds14_378.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_378 (by decide +kernel)

theorem valid14_384 : thresholds14_384.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_384 (by decide +kernel)

theorem valid14_390 : thresholds14_390.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_390 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part004

section Pack_Z6970H2307PackedBand14Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid14_396 : thresholds14_396.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_396 (by decide +kernel)

theorem valid14_402 : thresholds14_402.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_402 (by decide +kernel)

theorem valid14_408 : thresholds14_408.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_408 (by decide +kernel)

theorem valid14_414 : thresholds14_414.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_414 (by decide +kernel)

theorem valid14_420 : thresholds14_420.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_420 (by decide +kernel)

theorem valid14_426 : thresholds14_426.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_426 (by decide +kernel)

theorem valid14_432 : thresholds14_432.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_432 (by decide +kernel)

theorem valid14_438 : thresholds14_438.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_438 (by decide +kernel)

theorem valid14_444 : thresholds14_444.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_444 (by decide +kernel)

theorem valid14_450 : thresholds14_450.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_450 (by decide +kernel)

theorem valid14_456 : thresholds14_456.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_456 (by decide +kernel)

theorem valid14_462 : thresholds14_462.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_462 (by decide +kernel)

theorem valid14_468 : thresholds14_468.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_468 (by decide +kernel)

theorem valid14_474 : thresholds14_474.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_474 (by decide +kernel)

theorem valid14_480 : thresholds14_480.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_480 (by decide +kernel)

theorem valid14_486 : thresholds14_486.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_486 (by decide +kernel)

theorem valid14_492 : thresholds14_492.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_492 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part005

section Pack_Z6970H2307PackedBand14Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid14_498 : thresholds14_498.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_498 (by decide +kernel)

theorem valid14_504 : thresholds14_504.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_504 (by decide +kernel)

theorem valid14_510 : thresholds14_510.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_510 (by decide +kernel)

theorem valid14_516 : thresholds14_516.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_516 (by decide +kernel)

theorem valid14_522 : thresholds14_522.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_522 (by decide +kernel)

theorem valid14_528 : thresholds14_528.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_528 (by decide +kernel)

theorem valid14_534 : thresholds14_534.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_534 (by decide +kernel)

theorem valid14_540 : thresholds14_540.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_540 (by decide +kernel)

theorem valid14_546 : thresholds14_546.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_546 (by decide +kernel)

theorem valid14_552 : thresholds14_552.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_552 (by decide +kernel)

theorem valid14_558 : thresholds14_558.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_558 (by decide +kernel)

theorem valid14_564 : thresholds14_564.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_564 (by decide +kernel)

theorem valid14_570 : thresholds14_570.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_570 (by decide +kernel)

theorem valid14_576 : thresholds14_576.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_576 (by decide +kernel)

theorem valid14_582 : thresholds14_582.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_582 (by decide +kernel)

theorem valid14_588 : thresholds14_588.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_588 (by decide +kernel)

theorem valid14_594 : thresholds14_594.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_594 (by decide +kernel)

theorem valid14_600 : thresholds14_600.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_600 (by decide +kernel)

theorem valid14_606 : thresholds14_606.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_606 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part006

section Pack_Z6970H2307PackedBand14Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid14_612 : thresholds14_612.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_612 (by decide +kernel)

theorem valid14_618 : thresholds14_618.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_618 (by decide +kernel)

theorem valid14_624 : thresholds14_624.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_624 (by decide +kernel)

theorem valid14_630 : thresholds14_630.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_630 (by decide +kernel)

theorem valid14_636 : thresholds14_636.all (checked ⟨10,3,1⟩)=true :=
  checkedVerified ⟨10,3,1⟩ prefixMap14 thresholds14_636 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand14Part007

section Pack_Z6970H2307PackedBand15Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid15_0_0 : (thresholds15_0.take 3).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_0.take 3) (by decide +kernel)

private theorem valid15_0_3 : (thresholds15_0.drop 3).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_0.drop 3) (by decide +kernel)

theorem valid15_0 : thresholds15_0.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_0 3 valid15_0_0 (valid15_0_3)

theorem valid15_6 : thresholds15_6.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_6 (by decide +kernel)

theorem valid15_12 : thresholds15_12.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_12 (by decide +kernel)

theorem valid15_18 : thresholds15_18.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_18 (by decide +kernel)

theorem valid15_24 : thresholds15_24.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_24 (by decide +kernel)

private theorem valid15_30_0 : (thresholds15_30.take 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_30.take 4) (by decide +kernel)

private theorem valid15_30_4 : (thresholds15_30.drop 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_30.drop 4) (by decide +kernel)

theorem valid15_30 : thresholds15_30.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_30 4 valid15_30_0 (valid15_30_4)

private theorem valid15_36_0 : (thresholds15_36.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_36.take 5) (by decide +kernel)

private theorem valid15_36_5 : (thresholds15_36.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_36.drop 5) (by decide +kernel)

theorem valid15_36 : thresholds15_36.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_36 5 valid15_36_0 (valid15_36_5)

theorem valid15_42 : thresholds15_42.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_42 (by decide +kernel)

private theorem valid15_48_0 : (thresholds15_48.take 3).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_48.take 3) (by decide +kernel)

private theorem valid15_48_3 : (thresholds15_48.drop 3).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_48.drop 3) (by decide +kernel)

theorem valid15_48 : thresholds15_48.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_48 3 valid15_48_0 (valid15_48_3)

private theorem valid15_54_0 : (thresholds15_54.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_54.take 5) (by decide +kernel)

private theorem valid15_54_5 : (thresholds15_54.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_54.drop 5) (by decide +kernel)

theorem valid15_54 : thresholds15_54.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_54 5 valid15_54_0 (valid15_54_5)

private theorem valid15_60_0 : (thresholds15_60.take 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_60.take 4) (by decide +kernel)

private theorem valid15_60_4 : (thresholds15_60.drop 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_60.drop 4) (by decide +kernel)

theorem valid15_60 : thresholds15_60.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_60 4 valid15_60_0 (valid15_60_4)

theorem valid15_66 : thresholds15_66.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_66 (by decide +kernel)

private theorem valid15_72_0 : (thresholds15_72.take 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_72.take 4) (by decide +kernel)

private theorem valid15_72_4 : (thresholds15_72.drop 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_72.drop 4) (by decide +kernel)

theorem valid15_72 : thresholds15_72.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_72 4 valid15_72_0 (valid15_72_4)

theorem valid15_78 : thresholds15_78.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_78 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part000

section Pack_Z6970H2307PackedBand15Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid15_84_0 : (thresholds15_84.take 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_84.take 4) (by decide +kernel)

private theorem valid15_84_4 : (thresholds15_84.drop 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_84.drop 4) (by decide +kernel)

theorem valid15_84 : thresholds15_84.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_84 4 valid15_84_0 (valid15_84_4)

theorem valid15_90 : thresholds15_90.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_90 (by decide +kernel)

private theorem valid15_96_0 : (thresholds15_96.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_96.take 5) (by decide +kernel)

private theorem valid15_96_5 : (thresholds15_96.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_96.drop 5) (by decide +kernel)

theorem valid15_96 : thresholds15_96.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_96 5 valid15_96_0 (valid15_96_5)

private theorem valid15_102_0 : (thresholds15_102.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_102.take 5) (by decide +kernel)

private theorem valid15_102_5 : (thresholds15_102.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_102.drop 5) (by decide +kernel)

theorem valid15_102 : thresholds15_102.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_102 5 valid15_102_0 (valid15_102_5)

theorem valid15_108 : thresholds15_108.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_108 (by decide +kernel)

private theorem valid15_114_0 : (thresholds15_114.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_114.take 5) (by decide +kernel)

private theorem valid15_114_5 : (thresholds15_114.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_114.drop 5) (by decide +kernel)

theorem valid15_114 : thresholds15_114.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_114 5 valid15_114_0 (valid15_114_5)

theorem valid15_120 : thresholds15_120.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_120 (by decide +kernel)

private theorem valid15_126_0 : (thresholds15_126.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_126.take 5) (by decide +kernel)

private theorem valid15_126_5 : (thresholds15_126.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_126.drop 5) (by decide +kernel)

theorem valid15_126 : thresholds15_126.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_126 5 valid15_126_0 (valid15_126_5)

theorem valid15_132 : thresholds15_132.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_132 (by decide +kernel)

private theorem valid15_138_0 : (thresholds15_138.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_138.take 5) (by decide +kernel)

private theorem valid15_138_5 : (thresholds15_138.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_138.drop 5) (by decide +kernel)

theorem valid15_138 : thresholds15_138.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_138 5 valid15_138_0 (valid15_138_5)

theorem valid15_144 : thresholds15_144.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_144 (by decide +kernel)

private theorem valid15_150_0 : (thresholds15_150.take 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_150.take 4) (by decide +kernel)

private theorem valid15_150_4 : (thresholds15_150.drop 4).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_150.drop 4) (by decide +kernel)

theorem valid15_150 : thresholds15_150.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_150 4 valid15_150_0 (valid15_150_4)

theorem valid15_156 : thresholds15_156.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_156 (by decide +kernel)

theorem valid15_162 : thresholds15_162.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_162 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part001

section Pack_Z6970H2307PackedBand15Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid15_168 : thresholds15_168.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_168 (by decide +kernel)

private theorem valid15_174_0 : (thresholds15_174.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_174.take 5) (by decide +kernel)

private theorem valid15_174_5 : (thresholds15_174.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_174.drop 5) (by decide +kernel)

theorem valid15_174 : thresholds15_174.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_174 5 valid15_174_0 (valid15_174_5)

theorem valid15_180 : thresholds15_180.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_180 (by decide +kernel)

theorem valid15_186 : thresholds15_186.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_186 (by decide +kernel)

private theorem valid15_192_0 : (thresholds15_192.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_192.take 5) (by decide +kernel)

private theorem valid15_192_5 : (thresholds15_192.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_192.drop 5) (by decide +kernel)

theorem valid15_192 : thresholds15_192.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_192 5 valid15_192_0 (valid15_192_5)

theorem valid15_198 : thresholds15_198.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_198 (by decide +kernel)

theorem valid15_204 : thresholds15_204.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_204 (by decide +kernel)

private theorem valid15_210_0 : (thresholds15_210.take 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_210.take 5) (by decide +kernel)

private theorem valid15_210_5 : (thresholds15_210.drop 5).all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 (thresholds15_210.drop 5) (by decide +kernel)

theorem valid15_210 : thresholds15_210.all (checked ⟨21,3,1⟩)=true :=
  all_take_drop (checked ⟨21,3,1⟩) thresholds15_210 5 valid15_210_0 (valid15_210_5)

theorem valid15_216 : thresholds15_216.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_216 (by decide +kernel)

theorem valid15_222 : thresholds15_222.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_222 (by decide +kernel)

theorem valid15_228 : thresholds15_228.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_228 (by decide +kernel)

theorem valid15_234 : thresholds15_234.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_234 (by decide +kernel)

theorem valid15_240 : thresholds15_240.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_240 (by decide +kernel)

theorem valid15_246 : thresholds15_246.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_246 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part002

section Pack_Z6970H2307PackedBand15Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid15_252 : thresholds15_252.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_252 (by decide +kernel)

theorem valid15_258 : thresholds15_258.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_258 (by decide +kernel)

theorem valid15_264 : thresholds15_264.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_264 (by decide +kernel)

theorem valid15_270 : thresholds15_270.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_270 (by decide +kernel)

theorem valid15_276 : thresholds15_276.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_276 (by decide +kernel)

theorem valid15_282 : thresholds15_282.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_282 (by decide +kernel)

theorem valid15_288 : thresholds15_288.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_288 (by decide +kernel)

theorem valid15_294 : thresholds15_294.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_294 (by decide +kernel)

theorem valid15_300 : thresholds15_300.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_300 (by decide +kernel)

theorem valid15_306 : thresholds15_306.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_306 (by decide +kernel)

theorem valid15_312 : thresholds15_312.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_312 (by decide +kernel)

theorem valid15_318 : thresholds15_318.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_318 (by decide +kernel)

theorem valid15_324 : thresholds15_324.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_324 (by decide +kernel)

theorem valid15_330 : thresholds15_330.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_330 (by decide +kernel)

theorem valid15_336 : thresholds15_336.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_336 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part003

section Pack_Z6970H2307PackedBand15Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid15_342 : thresholds15_342.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_342 (by decide +kernel)

theorem valid15_348 : thresholds15_348.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_348 (by decide +kernel)

theorem valid15_354 : thresholds15_354.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_354 (by decide +kernel)

theorem valid15_360 : thresholds15_360.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_360 (by decide +kernel)

theorem valid15_366 : thresholds15_366.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_366 (by decide +kernel)

theorem valid15_372 : thresholds15_372.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_372 (by decide +kernel)

theorem valid15_378 : thresholds15_378.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_378 (by decide +kernel)

theorem valid15_384 : thresholds15_384.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_384 (by decide +kernel)

theorem valid15_390 : thresholds15_390.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_390 (by decide +kernel)

theorem valid15_396 : thresholds15_396.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_396 (by decide +kernel)

theorem valid15_402 : thresholds15_402.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_402 (by decide +kernel)

theorem valid15_408 : thresholds15_408.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_408 (by decide +kernel)

theorem valid15_414 : thresholds15_414.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_414 (by decide +kernel)

theorem valid15_420 : thresholds15_420.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_420 (by decide +kernel)

theorem valid15_426 : thresholds15_426.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_426 (by decide +kernel)

theorem valid15_432 : thresholds15_432.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_432 (by decide +kernel)

theorem valid15_438 : thresholds15_438.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_438 (by decide +kernel)

theorem valid15_444 : thresholds15_444.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_444 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part004

section Pack_Z6970H2307PackedBand15Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid15_450 : thresholds15_450.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_450 (by decide +kernel)

theorem valid15_456 : thresholds15_456.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_456 (by decide +kernel)

theorem valid15_462 : thresholds15_462.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_462 (by decide +kernel)

theorem valid15_468 : thresholds15_468.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_468 (by decide +kernel)

theorem valid15_474 : thresholds15_474.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_474 (by decide +kernel)

theorem valid15_480 : thresholds15_480.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_480 (by decide +kernel)

theorem valid15_486 : thresholds15_486.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_486 (by decide +kernel)

theorem valid15_492 : thresholds15_492.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_492 (by decide +kernel)

theorem valid15_498 : thresholds15_498.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_498 (by decide +kernel)

theorem valid15_504 : thresholds15_504.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_504 (by decide +kernel)

theorem valid15_510 : thresholds15_510.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_510 (by decide +kernel)

theorem valid15_516 : thresholds15_516.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_516 (by decide +kernel)

theorem valid15_522 : thresholds15_522.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_522 (by decide +kernel)

theorem valid15_528 : thresholds15_528.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_528 (by decide +kernel)

theorem valid15_534 : thresholds15_534.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_534 (by decide +kernel)

theorem valid15_540 : thresholds15_540.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_540 (by decide +kernel)

theorem valid15_546 : thresholds15_546.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_546 (by decide +kernel)

theorem valid15_552 : thresholds15_552.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_552 (by decide +kernel)

theorem valid15_558 : thresholds15_558.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_558 (by decide +kernel)

theorem valid15_564 : thresholds15_564.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_564 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part005

section Pack_Z6970H2307PackedBand15Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid15_570 : thresholds15_570.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_570 (by decide +kernel)

theorem valid15_576 : thresholds15_576.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_576 (by decide +kernel)

theorem valid15_582 : thresholds15_582.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_582 (by decide +kernel)

theorem valid15_588 : thresholds15_588.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_588 (by decide +kernel)

theorem valid15_594 : thresholds15_594.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_594 (by decide +kernel)

theorem valid15_600 : thresholds15_600.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_600 (by decide +kernel)

theorem valid15_606 : thresholds15_606.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_606 (by decide +kernel)

theorem valid15_612 : thresholds15_612.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_612 (by decide +kernel)

theorem valid15_618 : thresholds15_618.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_618 (by decide +kernel)

theorem valid15_624 : thresholds15_624.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_624 (by decide +kernel)

theorem valid15_630 : thresholds15_630.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_630 (by decide +kernel)

theorem valid15_636 : thresholds15_636.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_636 (by decide +kernel)

theorem valid15_642 : thresholds15_642.all (checked ⟨21,3,1⟩)=true :=
  checkedVerified ⟨21,3,1⟩ prefixMap15 thresholds15_642 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand15Part006

section Pack_Z6970H2307PackedBand16Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid16_0_0 : (thresholds16_0.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_0.take 4) (by decide +kernel)

private theorem valid16_0_4 : (thresholds16_0.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_0.drop 4) (by decide +kernel)

theorem valid16_0 : thresholds16_0.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_0 4 valid16_0_0 (valid16_0_4)

theorem valid16_6 : thresholds16_6.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_6 (by decide +kernel)

theorem valid16_12 : thresholds16_12.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_12 (by decide +kernel)

theorem valid16_18 : thresholds16_18.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_18 (by decide +kernel)

theorem valid16_24 : thresholds16_24.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_24 (by decide +kernel)

theorem valid16_30 : thresholds16_30.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_30 (by decide +kernel)

private theorem valid16_36_0 : (thresholds16_36.take 3).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_36.take 3) (by decide +kernel)

private theorem valid16_36_3 : (thresholds16_36.drop 3).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_36.drop 3) (by decide +kernel)

theorem valid16_36 : thresholds16_36.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_36 3 valid16_36_0 (valid16_36_3)

private theorem valid16_42_0 : (thresholds16_42.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_42.take 5) (by decide +kernel)

private theorem valid16_42_5 : (thresholds16_42.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_42.drop 5) (by decide +kernel)

theorem valid16_42 : thresholds16_42.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_42 5 valid16_42_0 (valid16_42_5)

private theorem valid16_48_0 : (thresholds16_48.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_48.take 4) (by decide +kernel)

private theorem valid16_48_4 : (thresholds16_48.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_48.drop 4) (by decide +kernel)

theorem valid16_48 : thresholds16_48.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_48 4 valid16_48_0 (valid16_48_4)

theorem valid16_54 : thresholds16_54.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_54 (by decide +kernel)

private theorem valid16_60_0 : (thresholds16_60.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_60.take 4) (by decide +kernel)

private theorem valid16_60_4 : (thresholds16_60.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_60.drop 4) (by decide +kernel)

theorem valid16_60 : thresholds16_60.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_60 4 valid16_60_0 (valid16_60_4)

theorem valid16_66 : thresholds16_66.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_66 (by decide +kernel)

private theorem valid16_72_0 : (thresholds16_72.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_72.take 4) (by decide +kernel)

private theorem valid16_72_4 : (thresholds16_72.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_72.drop 4) (by decide +kernel)

theorem valid16_72 : thresholds16_72.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_72 4 valid16_72_0 (valid16_72_4)

theorem valid16_78 : thresholds16_78.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_78 (by decide +kernel)

private theorem valid16_84_0 : (thresholds16_84.take 3).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_84.take 3) (by decide +kernel)

private theorem valid16_84_3 : (thresholds16_84.drop 3).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_84.drop 3) (by decide +kernel)

theorem valid16_84 : thresholds16_84.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_84 3 valid16_84_0 (valid16_84_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand16Part000

section Pack_Z6970H2307PackedBand16Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid16_90 : thresholds16_90.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_90 (by decide +kernel)

private theorem valid16_96_0 : (thresholds16_96.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_96.take 4) (by decide +kernel)

private theorem valid16_96_4 : (thresholds16_96.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_96.drop 4) (by decide +kernel)

theorem valid16_96 : thresholds16_96.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_96 4 valid16_96_0 (valid16_96_4)

private theorem valid16_102_0 : (thresholds16_102.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_102.take 4) (by decide +kernel)

private theorem valid16_102_4 : (thresholds16_102.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_102.drop 4) (by decide +kernel)

theorem valid16_102 : thresholds16_102.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_102 4 valid16_102_0 (valid16_102_4)

private theorem valid16_108_0 : (thresholds16_108.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_108.take 5) (by decide +kernel)

private theorem valid16_108_5 : (thresholds16_108.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_108.drop 5) (by decide +kernel)

theorem valid16_108 : thresholds16_108.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_108 5 valid16_108_0 (valid16_108_5)

theorem valid16_114 : thresholds16_114.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_114 (by decide +kernel)

private theorem valid16_120_0 : (thresholds16_120.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_120.take 4) (by decide +kernel)

private theorem valid16_120_4 : (thresholds16_120.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_120.drop 4) (by decide +kernel)

theorem valid16_120 : thresholds16_120.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_120 4 valid16_120_0 (valid16_120_4)

private theorem valid16_126_0 : (thresholds16_126.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_126.take 5) (by decide +kernel)

private theorem valid16_126_5 : (thresholds16_126.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_126.drop 5) (by decide +kernel)

theorem valid16_126 : thresholds16_126.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_126 5 valid16_126_0 (valid16_126_5)

theorem valid16_132 : thresholds16_132.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_132 (by decide +kernel)

private theorem valid16_138_0 : (thresholds16_138.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_138.take 5) (by decide +kernel)

private theorem valid16_138_5 : (thresholds16_138.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_138.drop 5) (by decide +kernel)

theorem valid16_138 : thresholds16_138.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_138 5 valid16_138_0 (valid16_138_5)

theorem valid16_144 : thresholds16_144.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_144 (by decide +kernel)

private theorem valid16_150_0 : (thresholds16_150.take 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_150.take 4) (by decide +kernel)

private theorem valid16_150_4 : (thresholds16_150.drop 4).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_150.drop 4) (by decide +kernel)

theorem valid16_150 : thresholds16_150.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_150 4 valid16_150_0 (valid16_150_4)

theorem valid16_156 : thresholds16_156.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_156 (by decide +kernel)

private theorem valid16_162_0 : (thresholds16_162.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_162.take 5) (by decide +kernel)

private theorem valid16_162_5 : (thresholds16_162.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_162.drop 5) (by decide +kernel)

theorem valid16_162 : thresholds16_162.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_162 5 valid16_162_0 (valid16_162_5)

theorem valid16_168 : thresholds16_168.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_168 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand16Part001

section Pack_Z6970H2307PackedBand16Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid16_174 : thresholds16_174.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_174 (by decide +kernel)

private theorem valid16_180_0 : (thresholds16_180.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_180.take 5) (by decide +kernel)

private theorem valid16_180_5 : (thresholds16_180.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_180.drop 5) (by decide +kernel)

theorem valid16_180 : thresholds16_180.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_180 5 valid16_180_0 (valid16_180_5)

private theorem valid16_186_0 : (thresholds16_186.take 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_186.take 5) (by decide +kernel)

private theorem valid16_186_5 : (thresholds16_186.drop 5).all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 (thresholds16_186.drop 5) (by decide +kernel)

theorem valid16_186 : thresholds16_186.all (checked ⟨14,4,1⟩)=true :=
  all_take_drop (checked ⟨14,4,1⟩) thresholds16_186 5 valid16_186_0 (valid16_186_5)

theorem valid16_192 : thresholds16_192.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_192 (by decide +kernel)

theorem valid16_198 : thresholds16_198.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_198 (by decide +kernel)

theorem valid16_204 : thresholds16_204.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_204 (by decide +kernel)

theorem valid16_210 : thresholds16_210.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_210 (by decide +kernel)

theorem valid16_216 : thresholds16_216.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_216 (by decide +kernel)

theorem valid16_222 : thresholds16_222.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_222 (by decide +kernel)

theorem valid16_228 : thresholds16_228.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_228 (by decide +kernel)

theorem valid16_234 : thresholds16_234.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_234 (by decide +kernel)

theorem valid16_240 : thresholds16_240.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_240 (by decide +kernel)

theorem valid16_246 : thresholds16_246.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_246 (by decide +kernel)

theorem valid16_252 : thresholds16_252.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_252 (by decide +kernel)

theorem valid16_258 : thresholds16_258.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_258 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand16Part002

section Pack_Z6970H2307PackedBand16Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid16_264 : thresholds16_264.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_264 (by decide +kernel)

theorem valid16_270 : thresholds16_270.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_270 (by decide +kernel)

theorem valid16_276 : thresholds16_276.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_276 (by decide +kernel)

theorem valid16_282 : thresholds16_282.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_282 (by decide +kernel)

theorem valid16_288 : thresholds16_288.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_288 (by decide +kernel)

theorem valid16_294 : thresholds16_294.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_294 (by decide +kernel)

theorem valid16_300 : thresholds16_300.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_300 (by decide +kernel)

theorem valid16_306 : thresholds16_306.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_306 (by decide +kernel)

theorem valid16_312 : thresholds16_312.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_312 (by decide +kernel)

theorem valid16_318 : thresholds16_318.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_318 (by decide +kernel)

theorem valid16_324 : thresholds16_324.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_324 (by decide +kernel)

theorem valid16_330 : thresholds16_330.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_330 (by decide +kernel)

theorem valid16_336 : thresholds16_336.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_336 (by decide +kernel)

theorem valid16_342 : thresholds16_342.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_342 (by decide +kernel)

theorem valid16_348 : thresholds16_348.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_348 (by decide +kernel)

theorem valid16_354 : thresholds16_354.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_354 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand16Part003

section Pack_Z6970H2307PackedBand16Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid16_360 : thresholds16_360.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_360 (by decide +kernel)

theorem valid16_366 : thresholds16_366.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_366 (by decide +kernel)

theorem valid16_372 : thresholds16_372.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_372 (by decide +kernel)

theorem valid16_378 : thresholds16_378.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_378 (by decide +kernel)

theorem valid16_384 : thresholds16_384.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_384 (by decide +kernel)

theorem valid16_390 : thresholds16_390.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_390 (by decide +kernel)

theorem valid16_396 : thresholds16_396.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_396 (by decide +kernel)

theorem valid16_402 : thresholds16_402.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_402 (by decide +kernel)

theorem valid16_408 : thresholds16_408.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_408 (by decide +kernel)

theorem valid16_414 : thresholds16_414.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_414 (by decide +kernel)

theorem valid16_420 : thresholds16_420.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_420 (by decide +kernel)

theorem valid16_426 : thresholds16_426.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_426 (by decide +kernel)

theorem valid16_432 : thresholds16_432.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_432 (by decide +kernel)

theorem valid16_438 : thresholds16_438.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_438 (by decide +kernel)

theorem valid16_444 : thresholds16_444.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_444 (by decide +kernel)

theorem valid16_450 : thresholds16_450.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_450 (by decide +kernel)

theorem valid16_456 : thresholds16_456.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_456 (by decide +kernel)

theorem valid16_462 : thresholds16_462.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_462 (by decide +kernel)

theorem valid16_468 : thresholds16_468.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_468 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand16Part004

section Pack_Z6970H2307PackedBand16Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid16_474 : thresholds16_474.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_474 (by decide +kernel)

theorem valid16_480 : thresholds16_480.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_480 (by decide +kernel)

theorem valid16_486 : thresholds16_486.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_486 (by decide +kernel)

theorem valid16_492 : thresholds16_492.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_492 (by decide +kernel)

theorem valid16_498 : thresholds16_498.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_498 (by decide +kernel)

theorem valid16_504 : thresholds16_504.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_504 (by decide +kernel)

theorem valid16_510 : thresholds16_510.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_510 (by decide +kernel)

theorem valid16_516 : thresholds16_516.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_516 (by decide +kernel)

theorem valid16_522 : thresholds16_522.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_522 (by decide +kernel)

theorem valid16_528 : thresholds16_528.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_528 (by decide +kernel)

theorem valid16_534 : thresholds16_534.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_534 (by decide +kernel)

theorem valid16_540 : thresholds16_540.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_540 (by decide +kernel)

theorem valid16_546 : thresholds16_546.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_546 (by decide +kernel)

theorem valid16_552 : thresholds16_552.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_552 (by decide +kernel)

theorem valid16_558 : thresholds16_558.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_558 (by decide +kernel)

theorem valid16_564 : thresholds16_564.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_564 (by decide +kernel)

theorem valid16_570 : thresholds16_570.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_570 (by decide +kernel)

theorem valid16_576 : thresholds16_576.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_576 (by decide +kernel)

theorem valid16_582 : thresholds16_582.all (checked ⟨14,4,1⟩)=true :=
  checkedVerified ⟨14,4,1⟩ prefixMap16 thresholds16_582 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand16Part005

section Pack_Z6970H2307PackedBand17Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid17_0_0 : (thresholds17_0.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_0.take 4) (by decide +kernel)

private theorem valid17_0_4 : (thresholds17_0.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_0.drop 4) (by decide +kernel)

theorem valid17_0 : thresholds17_0.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_0 4 valid17_0_0 (valid17_0_4)

private theorem valid17_6_0 : (thresholds17_6.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_6.take 3) (by decide +kernel)

private theorem valid17_6_3 : (thresholds17_6.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_6.drop 3) (by decide +kernel)

theorem valid17_6 : thresholds17_6.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_6 3 valid17_6_0 (valid17_6_3)

theorem valid17_12 : thresholds17_12.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_12 (by decide +kernel)

theorem valid17_18 : thresholds17_18.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_18 (by decide +kernel)

private theorem valid17_24_0 : (thresholds17_24.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_24.take 4) (by decide +kernel)

private theorem valid17_24_4 : ((thresholds17_24.drop 4).take 1).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 ((thresholds17_24.drop 4).take 1) (by decide +kernel)

private theorem valid17_24_5 : (thresholds17_24.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_24.drop 5) (by decide +kernel)

theorem valid17_24 : thresholds17_24.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_24 4 valid17_24_0 (all_take_drop (checked ⟨2,5,1⟩) (thresholds17_24.drop 4) 1 valid17_24_4 (valid17_24_5))

private theorem valid17_30_0 : (thresholds17_30.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_30.take 5) (by decide +kernel)

private theorem valid17_30_5 : (thresholds17_30.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_30.drop 5) (by decide +kernel)

theorem valid17_30 : thresholds17_30.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_30 5 valid17_30_0 (valid17_30_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part000

section Pack_Z6970H2307PackedBand17Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid17_36_0 : (thresholds17_36.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_36.take 4) (by decide +kernel)

private theorem valid17_36_4 : ((thresholds17_36.drop 4).take 1).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 ((thresholds17_36.drop 4).take 1) (by decide +kernel)

private theorem valid17_36_5 : (thresholds17_36.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_36.drop 5) (by decide +kernel)

theorem valid17_36 : thresholds17_36.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_36 4 valid17_36_0 (all_take_drop (checked ⟨2,5,1⟩) (thresholds17_36.drop 4) 1 valid17_36_4 (valid17_36_5))

private theorem valid17_42_0 : (thresholds17_42.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_42.take 4) (by decide +kernel)

private theorem valid17_42_4 : (thresholds17_42.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_42.drop 4) (by decide +kernel)

theorem valid17_42 : thresholds17_42.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_42 4 valid17_42_0 (valid17_42_4)

private theorem valid17_48_0 : (thresholds17_48.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_48.take 5) (by decide +kernel)

private theorem valid17_48_5 : (thresholds17_48.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_48.drop 5) (by decide +kernel)

theorem valid17_48 : thresholds17_48.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_48 5 valid17_48_0 (valid17_48_5)

private theorem valid17_54_0 : (thresholds17_54.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_54.take 4) (by decide +kernel)

private theorem valid17_54_4 : (thresholds17_54.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_54.drop 4) (by decide +kernel)

theorem valid17_54 : thresholds17_54.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_54 4 valid17_54_0 (valid17_54_4)

private theorem valid17_60_0 : (thresholds17_60.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_60.take 3) (by decide +kernel)

private theorem valid17_60_3 : (thresholds17_60.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_60.drop 3) (by decide +kernel)

theorem valid17_60 : thresholds17_60.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_60 3 valid17_60_0 (valid17_60_3)

private theorem valid17_66_0 : (thresholds17_66.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_66.take 3) (by decide +kernel)

private theorem valid17_66_3 : (thresholds17_66.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_66.drop 3) (by decide +kernel)

theorem valid17_66 : thresholds17_66.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_66 3 valid17_66_0 (valid17_66_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part001

section Pack_Z6970H2307PackedBand17Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid17_72_0 : (thresholds17_72.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_72.take 4) (by decide +kernel)

private theorem valid17_72_4 : ((thresholds17_72.drop 4).take 1).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 ((thresholds17_72.drop 4).take 1) (by decide +kernel)

private theorem valid17_72_5 : (thresholds17_72.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_72.drop 5) (by decide +kernel)

theorem valid17_72 : thresholds17_72.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_72 4 valid17_72_0 (all_take_drop (checked ⟨2,5,1⟩) (thresholds17_72.drop 4) 1 valid17_72_4 (valid17_72_5))

private theorem valid17_78_0 : (thresholds17_78.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_78.take 3) (by decide +kernel)

private theorem valid17_78_3 : (thresholds17_78.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_78.drop 3) (by decide +kernel)

theorem valid17_78 : thresholds17_78.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_78 3 valid17_78_0 (valid17_78_3)

private theorem valid17_84_0 : (thresholds17_84.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_84.take 4) (by decide +kernel)

private theorem valid17_84_4 : (thresholds17_84.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_84.drop 4) (by decide +kernel)

theorem valid17_84 : thresholds17_84.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_84 4 valid17_84_0 (valid17_84_4)

private theorem valid17_90_0 : (thresholds17_90.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_90.take 4) (by decide +kernel)

private theorem valid17_90_4 : (thresholds17_90.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_90.drop 4) (by decide +kernel)

theorem valid17_90 : thresholds17_90.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_90 4 valid17_90_0 (valid17_90_4)

private theorem valid17_96_0 : (thresholds17_96.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_96.take 5) (by decide +kernel)

private theorem valid17_96_5 : (thresholds17_96.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_96.drop 5) (by decide +kernel)

theorem valid17_96 : thresholds17_96.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_96 5 valid17_96_0 (valid17_96_5)

private theorem valid17_102_0 : (thresholds17_102.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_102.take 5) (by decide +kernel)

private theorem valid17_102_5 : (thresholds17_102.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_102.drop 5) (by decide +kernel)

theorem valid17_102 : thresholds17_102.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_102 5 valid17_102_0 (valid17_102_5)

private theorem valid17_108_0 : (thresholds17_108.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_108.take 4) (by decide +kernel)

private theorem valid17_108_4 : (thresholds17_108.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_108.drop 4) (by decide +kernel)

theorem valid17_108 : thresholds17_108.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_108 4 valid17_108_0 (valid17_108_4)

private theorem valid17_114_0 : (thresholds17_114.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_114.take 5) (by decide +kernel)

private theorem valid17_114_5 : (thresholds17_114.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_114.drop 5) (by decide +kernel)

theorem valid17_114 : thresholds17_114.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_114 5 valid17_114_0 (valid17_114_5)

private theorem valid17_120_0 : (thresholds17_120.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_120.take 4) (by decide +kernel)

private theorem valid17_120_4 : (thresholds17_120.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_120.drop 4) (by decide +kernel)

theorem valid17_120 : thresholds17_120.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_120 4 valid17_120_0 (valid17_120_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part002

section Pack_Z6970H2307PackedBand17Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid17_126_0 : (thresholds17_126.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_126.take 3) (by decide +kernel)

private theorem valid17_126_3 : (thresholds17_126.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_126.drop 3) (by decide +kernel)

theorem valid17_126 : thresholds17_126.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_126 3 valid17_126_0 (valid17_126_3)

private theorem valid17_132_0 : (thresholds17_132.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_132.take 4) (by decide +kernel)

private theorem valid17_132_4 : (thresholds17_132.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_132.drop 4) (by decide +kernel)

theorem valid17_132 : thresholds17_132.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_132 4 valid17_132_0 (valid17_132_4)

private theorem valid17_138_0 : (thresholds17_138.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_138.take 3) (by decide +kernel)

private theorem valid17_138_3 : (thresholds17_138.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_138.drop 3) (by decide +kernel)

theorem valid17_138 : thresholds17_138.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_138 3 valid17_138_0 (valid17_138_3)

private theorem valid17_144_0 : (thresholds17_144.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_144.take 4) (by decide +kernel)

private theorem valid17_144_4 : (thresholds17_144.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_144.drop 4) (by decide +kernel)

theorem valid17_144 : thresholds17_144.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_144 4 valid17_144_0 (valid17_144_4)

private theorem valid17_150_0 : (thresholds17_150.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_150.take 4) (by decide +kernel)

private theorem valid17_150_4 : (thresholds17_150.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_150.drop 4) (by decide +kernel)

theorem valid17_150 : thresholds17_150.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_150 4 valid17_150_0 (valid17_150_4)

private theorem valid17_156_0 : (thresholds17_156.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_156.take 4) (by decide +kernel)

private theorem valid17_156_4 : (thresholds17_156.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_156.drop 4) (by decide +kernel)

theorem valid17_156 : thresholds17_156.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_156 4 valid17_156_0 (valid17_156_4)

private theorem valid17_162_0 : (thresholds17_162.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_162.take 4) (by decide +kernel)

private theorem valid17_162_4 : (thresholds17_162.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_162.drop 4) (by decide +kernel)

theorem valid17_162 : thresholds17_162.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_162 4 valid17_162_0 (valid17_162_4)

private theorem valid17_168_0 : (thresholds17_168.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_168.take 5) (by decide +kernel)

private theorem valid17_168_5 : (thresholds17_168.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_168.drop 5) (by decide +kernel)

theorem valid17_168 : thresholds17_168.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_168 5 valid17_168_0 (valid17_168_5)

private theorem valid17_174_0 : (thresholds17_174.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_174.take 5) (by decide +kernel)

private theorem valid17_174_5 : (thresholds17_174.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_174.drop 5) (by decide +kernel)

theorem valid17_174 : thresholds17_174.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_174 5 valid17_174_0 (valid17_174_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part003

section Pack_Z6970H2307PackedBand17Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid17_180_0 : (thresholds17_180.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_180.take 5) (by decide +kernel)

private theorem valid17_180_5 : (thresholds17_180.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_180.drop 5) (by decide +kernel)

theorem valid17_180 : thresholds17_180.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_180 5 valid17_180_0 (valid17_180_5)

private theorem valid17_186_0 : (thresholds17_186.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_186.take 5) (by decide +kernel)

private theorem valid17_186_5 : (thresholds17_186.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_186.drop 5) (by decide +kernel)

theorem valid17_186 : thresholds17_186.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_186 5 valid17_186_0 (valid17_186_5)

private theorem valid17_192_0 : (thresholds17_192.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_192.take 5) (by decide +kernel)

private theorem valid17_192_5 : (thresholds17_192.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_192.drop 5) (by decide +kernel)

theorem valid17_192 : thresholds17_192.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_192 5 valid17_192_0 (valid17_192_5)

private theorem valid17_198_0 : (thresholds17_198.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_198.take 5) (by decide +kernel)

private theorem valid17_198_5 : (thresholds17_198.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_198.drop 5) (by decide +kernel)

theorem valid17_198 : thresholds17_198.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_198 5 valid17_198_0 (valid17_198_5)

private theorem valid17_204_0 : (thresholds17_204.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_204.take 4) (by decide +kernel)

private theorem valid17_204_4 : (thresholds17_204.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_204.drop 4) (by decide +kernel)

theorem valid17_204 : thresholds17_204.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_204 4 valid17_204_0 (valid17_204_4)

private theorem valid17_210_0 : (thresholds17_210.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_210.take 4) (by decide +kernel)

private theorem valid17_210_4 : (thresholds17_210.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_210.drop 4) (by decide +kernel)

theorem valid17_210 : thresholds17_210.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_210 4 valid17_210_0 (valid17_210_4)

private theorem valid17_216_0 : (thresholds17_216.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_216.take 5) (by decide +kernel)

private theorem valid17_216_5 : (thresholds17_216.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_216.drop 5) (by decide +kernel)

theorem valid17_216 : thresholds17_216.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_216 5 valid17_216_0 (valid17_216_5)

private theorem valid17_222_0 : (thresholds17_222.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_222.take 5) (by decide +kernel)

private theorem valid17_222_5 : (thresholds17_222.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_222.drop 5) (by decide +kernel)

theorem valid17_222 : thresholds17_222.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_222 5 valid17_222_0 (valid17_222_5)

theorem valid17_228 : thresholds17_228.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_228 (by decide +kernel)

theorem valid17_234 : thresholds17_234.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_234 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part004

section Pack_Z6970H2307PackedBand17Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid17_240_0 : (thresholds17_240.take 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_240.take 5) (by decide +kernel)

private theorem valid17_240_5 : (thresholds17_240.drop 5).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_240.drop 5) (by decide +kernel)

theorem valid17_240 : thresholds17_240.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_240 5 valid17_240_0 (valid17_240_5)

private theorem valid17_246_0 : (thresholds17_246.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_246.take 4) (by decide +kernel)

private theorem valid17_246_4 : (thresholds17_246.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_246.drop 4) (by decide +kernel)

theorem valid17_246 : thresholds17_246.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_246 4 valid17_246_0 (valid17_246_4)

theorem valid17_252 : thresholds17_252.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_252 (by decide +kernel)

theorem valid17_258 : thresholds17_258.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_258 (by decide +kernel)

private theorem valid17_264_0 : (thresholds17_264.take 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_264.take 3) (by decide +kernel)

private theorem valid17_264_3 : (thresholds17_264.drop 3).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_264.drop 3) (by decide +kernel)

theorem valid17_264 : thresholds17_264.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_264 3 valid17_264_0 (valid17_264_3)

theorem valid17_270 : thresholds17_270.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_270 (by decide +kernel)

theorem valid17_276 : thresholds17_276.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_276 (by decide +kernel)

theorem valid17_282 : thresholds17_282.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_282 (by decide +kernel)

theorem valid17_288 : thresholds17_288.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_288 (by decide +kernel)

theorem valid17_294 : thresholds17_294.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_294 (by decide +kernel)

theorem valid17_300 : thresholds17_300.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_300 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part005

section Pack_Z6970H2307PackedBand17Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid17_306 : thresholds17_306.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_306 (by decide +kernel)

theorem valid17_312 : thresholds17_312.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_312 (by decide +kernel)

theorem valid17_318 : thresholds17_318.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_318 (by decide +kernel)

theorem valid17_324 : thresholds17_324.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_324 (by decide +kernel)

theorem valid17_330 : thresholds17_330.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_330 (by decide +kernel)

theorem valid17_336 : thresholds17_336.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_336 (by decide +kernel)

private theorem valid17_342_0 : (thresholds17_342.take 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_342.take 4) (by decide +kernel)

private theorem valid17_342_4 : (thresholds17_342.drop 4).all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 (thresholds17_342.drop 4) (by decide +kernel)

theorem valid17_342 : thresholds17_342.all (checked ⟨2,5,1⟩)=true :=
  all_take_drop (checked ⟨2,5,1⟩) thresholds17_342 4 valid17_342_0 (valid17_342_4)

theorem valid17_348 : thresholds17_348.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_348 (by decide +kernel)

theorem valid17_354 : thresholds17_354.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_354 (by decide +kernel)

theorem valid17_360 : thresholds17_360.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_360 (by decide +kernel)

theorem valid17_366 : thresholds17_366.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_366 (by decide +kernel)

theorem valid17_372 : thresholds17_372.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_372 (by decide +kernel)

theorem valid17_378 : thresholds17_378.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_378 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part006

section Pack_Z6970H2307PackedBand17Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid17_384 : thresholds17_384.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_384 (by decide +kernel)

theorem valid17_390 : thresholds17_390.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_390 (by decide +kernel)

theorem valid17_396 : thresholds17_396.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_396 (by decide +kernel)

theorem valid17_402 : thresholds17_402.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_402 (by decide +kernel)

theorem valid17_408 : thresholds17_408.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_408 (by decide +kernel)

theorem valid17_414 : thresholds17_414.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_414 (by decide +kernel)

theorem valid17_420 : thresholds17_420.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_420 (by decide +kernel)

theorem valid17_426 : thresholds17_426.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_426 (by decide +kernel)

theorem valid17_432 : thresholds17_432.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_432 (by decide +kernel)

theorem valid17_438 : thresholds17_438.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_438 (by decide +kernel)

theorem valid17_444 : thresholds17_444.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_444 (by decide +kernel)

theorem valid17_450 : thresholds17_450.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_450 (by decide +kernel)

theorem valid17_456 : thresholds17_456.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_456 (by decide +kernel)

theorem valid17_462 : thresholds17_462.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_462 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part007

section Pack_Z6970H2307PackedBand17Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid17_468 : thresholds17_468.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_468 (by decide +kernel)

theorem valid17_474 : thresholds17_474.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_474 (by decide +kernel)

theorem valid17_480 : thresholds17_480.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_480 (by decide +kernel)

theorem valid17_486 : thresholds17_486.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_486 (by decide +kernel)

theorem valid17_492 : thresholds17_492.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_492 (by decide +kernel)

theorem valid17_498 : thresholds17_498.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_498 (by decide +kernel)

theorem valid17_504 : thresholds17_504.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_504 (by decide +kernel)

theorem valid17_510 : thresholds17_510.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_510 (by decide +kernel)

theorem valid17_516 : thresholds17_516.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_516 (by decide +kernel)

theorem valid17_522 : thresholds17_522.all (checked ⟨2,5,1⟩)=true :=
  checkedVerified ⟨2,5,1⟩ prefixMap17 thresholds17_522 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand17Part008

section Pack_Z6970H2307PackedBand18Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid18_0_0 : (thresholds18_0.take 3).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_0.take 3) (by decide +kernel)

private theorem valid18_0_3 : (thresholds18_0.drop 3).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_0.drop 3) (by decide +kernel)

theorem valid18_0 : thresholds18_0.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_0 3 valid18_0_0 (valid18_0_3)

theorem valid18_6 : thresholds18_6.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_6 (by decide +kernel)

theorem valid18_12 : thresholds18_12.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_12 (by decide +kernel)

theorem valid18_18 : thresholds18_18.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_18 (by decide +kernel)

theorem valid18_24 : thresholds18_24.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_24 (by decide +kernel)

private theorem valid18_30_0 : (thresholds18_30.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_30.take 5) (by decide +kernel)

private theorem valid18_30_5 : (thresholds18_30.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_30.drop 5) (by decide +kernel)

theorem valid18_30 : thresholds18_30.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_30 5 valid18_30_0 (valid18_30_5)

theorem valid18_36 : thresholds18_36.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_36 (by decide +kernel)

private theorem valid18_42_0 : (thresholds18_42.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_42.take 5) (by decide +kernel)

private theorem valid18_42_5 : (thresholds18_42.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_42.drop 5) (by decide +kernel)

theorem valid18_42 : thresholds18_42.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_42 5 valid18_42_0 (valid18_42_5)

private theorem valid18_48_0 : (thresholds18_48.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_48.take 5) (by decide +kernel)

private theorem valid18_48_5 : (thresholds18_48.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_48.drop 5) (by decide +kernel)

theorem valid18_48 : thresholds18_48.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_48 5 valid18_48_0 (valid18_48_5)

private theorem valid18_54_0 : (thresholds18_54.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_54.take 5) (by decide +kernel)

private theorem valid18_54_5 : (thresholds18_54.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_54.drop 5) (by decide +kernel)

theorem valid18_54 : thresholds18_54.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_54 5 valid18_54_0 (valid18_54_5)

private theorem valid18_60_0 : (thresholds18_60.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_60.take 5) (by decide +kernel)

private theorem valid18_60_5 : (thresholds18_60.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_60.drop 5) (by decide +kernel)

theorem valid18_60 : thresholds18_60.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_60 5 valid18_60_0 (valid18_60_5)

private theorem valid18_66_0 : (thresholds18_66.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_66.take 5) (by decide +kernel)

private theorem valid18_66_5 : (thresholds18_66.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_66.drop 5) (by decide +kernel)

theorem valid18_66 : thresholds18_66.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_66 5 valid18_66_0 (valid18_66_5)

private theorem valid18_72_0 : (thresholds18_72.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_72.take 5) (by decide +kernel)

private theorem valid18_72_5 : (thresholds18_72.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_72.drop 5) (by decide +kernel)

theorem valid18_72 : thresholds18_72.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_72 5 valid18_72_0 (valid18_72_5)

private theorem valid18_78_0 : (thresholds18_78.take 4).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_78.take 4) (by decide +kernel)

private theorem valid18_78_4 : (thresholds18_78.drop 4).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_78.drop 4) (by decide +kernel)

theorem valid18_78 : thresholds18_78.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_78 4 valid18_78_0 (valid18_78_4)

private theorem valid18_84_0 : (thresholds18_84.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_84.take 5) (by decide +kernel)

private theorem valid18_84_5 : (thresholds18_84.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_84.drop 5) (by decide +kernel)

theorem valid18_84 : thresholds18_84.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_84 5 valid18_84_0 (valid18_84_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand18Part000

section Pack_Z6970H2307PackedBand18Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid18_90_0 : (thresholds18_90.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_90.take 5) (by decide +kernel)

private theorem valid18_90_5 : (thresholds18_90.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_90.drop 5) (by decide +kernel)

theorem valid18_90 : thresholds18_90.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_90 5 valid18_90_0 (valid18_90_5)

private theorem valid18_96_0 : (thresholds18_96.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_96.take 5) (by decide +kernel)

private theorem valid18_96_5 : (thresholds18_96.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_96.drop 5) (by decide +kernel)

theorem valid18_96 : thresholds18_96.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_96 5 valid18_96_0 (valid18_96_5)

private theorem valid18_102_0 : (thresholds18_102.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_102.take 5) (by decide +kernel)

private theorem valid18_102_5 : (thresholds18_102.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_102.drop 5) (by decide +kernel)

theorem valid18_102 : thresholds18_102.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_102 5 valid18_102_0 (valid18_102_5)

theorem valid18_108 : thresholds18_108.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_108 (by decide +kernel)

private theorem valid18_114_0 : (thresholds18_114.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_114.take 5) (by decide +kernel)

private theorem valid18_114_5 : (thresholds18_114.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_114.drop 5) (by decide +kernel)

theorem valid18_114 : thresholds18_114.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_114 5 valid18_114_0 (valid18_114_5)

private theorem valid18_120_0 : (thresholds18_120.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_120.take 5) (by decide +kernel)

private theorem valid18_120_5 : (thresholds18_120.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_120.drop 5) (by decide +kernel)

theorem valid18_120 : thresholds18_120.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_120 5 valid18_120_0 (valid18_120_5)

private theorem valid18_126_0 : (thresholds18_126.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_126.take 5) (by decide +kernel)

private theorem valid18_126_5 : (thresholds18_126.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_126.drop 5) (by decide +kernel)

theorem valid18_126 : thresholds18_126.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_126 5 valid18_126_0 (valid18_126_5)

theorem valid18_132 : thresholds18_132.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_132 (by decide +kernel)

private theorem valid18_138_0 : (thresholds18_138.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_138.take 5) (by decide +kernel)

private theorem valid18_138_5 : (thresholds18_138.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_138.drop 5) (by decide +kernel)

theorem valid18_138 : thresholds18_138.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_138 5 valid18_138_0 (valid18_138_5)

theorem valid18_144 : thresholds18_144.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_144 (by decide +kernel)

theorem valid18_150 : thresholds18_150.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_150 (by decide +kernel)

theorem valid18_156 : thresholds18_156.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_156 (by decide +kernel)

theorem valid18_162 : thresholds18_162.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_162 (by decide +kernel)

theorem valid18_168 : thresholds18_168.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_168 (by decide +kernel)

theorem valid18_174 : thresholds18_174.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_174 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand18Part001

section Pack_Z6970H2307PackedBand18Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid18_180_0 : (thresholds18_180.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_180.take 5) (by decide +kernel)

private theorem valid18_180_5 : (thresholds18_180.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_180.drop 5) (by decide +kernel)

theorem valid18_180 : thresholds18_180.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_180 5 valid18_180_0 (valid18_180_5)

theorem valid18_186 : thresholds18_186.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_186 (by decide +kernel)

private theorem valid18_192_0 : (thresholds18_192.take 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_192.take 5) (by decide +kernel)

private theorem valid18_192_5 : (thresholds18_192.drop 5).all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 (thresholds18_192.drop 5) (by decide +kernel)

theorem valid18_192 : thresholds18_192.all (checked ⟨10,5,1⟩)=true :=
  all_take_drop (checked ⟨10,5,1⟩) thresholds18_192 5 valid18_192_0 (valid18_192_5)

theorem valid18_198 : thresholds18_198.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_198 (by decide +kernel)

theorem valid18_204 : thresholds18_204.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_204 (by decide +kernel)

theorem valid18_210 : thresholds18_210.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_210 (by decide +kernel)

theorem valid18_216 : thresholds18_216.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_216 (by decide +kernel)

theorem valid18_222 : thresholds18_222.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_222 (by decide +kernel)

theorem valid18_228 : thresholds18_228.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_228 (by decide +kernel)

theorem valid18_234 : thresholds18_234.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_234 (by decide +kernel)

theorem valid18_240 : thresholds18_240.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_240 (by decide +kernel)

theorem valid18_246 : thresholds18_246.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_246 (by decide +kernel)

theorem valid18_252 : thresholds18_252.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_252 (by decide +kernel)

theorem valid18_258 : thresholds18_258.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_258 (by decide +kernel)

theorem valid18_264 : thresholds18_264.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_264 (by decide +kernel)

theorem valid18_270 : thresholds18_270.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_270 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand18Part002

section Pack_Z6970H2307PackedBand18Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid18_276 : thresholds18_276.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_276 (by decide +kernel)

theorem valid18_282 : thresholds18_282.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_282 (by decide +kernel)

theorem valid18_288 : thresholds18_288.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_288 (by decide +kernel)

theorem valid18_294 : thresholds18_294.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_294 (by decide +kernel)

theorem valid18_300 : thresholds18_300.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_300 (by decide +kernel)

theorem valid18_306 : thresholds18_306.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_306 (by decide +kernel)

theorem valid18_312 : thresholds18_312.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_312 (by decide +kernel)

theorem valid18_318 : thresholds18_318.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_318 (by decide +kernel)

theorem valid18_324 : thresholds18_324.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_324 (by decide +kernel)

theorem valid18_330 : thresholds18_330.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_330 (by decide +kernel)

theorem valid18_336 : thresholds18_336.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_336 (by decide +kernel)

theorem valid18_342 : thresholds18_342.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_342 (by decide +kernel)

theorem valid18_348 : thresholds18_348.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_348 (by decide +kernel)

theorem valid18_354 : thresholds18_354.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_354 (by decide +kernel)

theorem valid18_360 : thresholds18_360.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_360 (by decide +kernel)

theorem valid18_366 : thresholds18_366.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_366 (by decide +kernel)

theorem valid18_372 : thresholds18_372.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_372 (by decide +kernel)

theorem valid18_378 : thresholds18_378.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_378 (by decide +kernel)

theorem valid18_384 : thresholds18_384.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_384 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand18Part003

section Pack_Z6970H2307PackedBand18Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid18_390 : thresholds18_390.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_390 (by decide +kernel)

theorem valid18_396 : thresholds18_396.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_396 (by decide +kernel)

theorem valid18_402 : thresholds18_402.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_402 (by decide +kernel)

theorem valid18_408 : thresholds18_408.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_408 (by decide +kernel)

theorem valid18_414 : thresholds18_414.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_414 (by decide +kernel)

theorem valid18_420 : thresholds18_420.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_420 (by decide +kernel)

theorem valid18_426 : thresholds18_426.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_426 (by decide +kernel)

theorem valid18_432 : thresholds18_432.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_432 (by decide +kernel)

theorem valid18_438 : thresholds18_438.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_438 (by decide +kernel)

theorem valid18_444 : thresholds18_444.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_444 (by decide +kernel)

theorem valid18_450 : thresholds18_450.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_450 (by decide +kernel)

theorem valid18_456 : thresholds18_456.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_456 (by decide +kernel)

theorem valid18_462 : thresholds18_462.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_462 (by decide +kernel)

theorem valid18_468 : thresholds18_468.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_468 (by decide +kernel)

theorem valid18_474 : thresholds18_474.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_474 (by decide +kernel)

theorem valid18_480 : thresholds18_480.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_480 (by decide +kernel)

theorem valid18_486 : thresholds18_486.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_486 (by decide +kernel)

theorem valid18_492 : thresholds18_492.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_492 (by decide +kernel)

theorem valid18_498 : thresholds18_498.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_498 (by decide +kernel)

theorem valid18_504 : thresholds18_504.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_504 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand18Part004

section Pack_Z6970H2307PackedBand18Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid18_510 : thresholds18_510.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_510 (by decide +kernel)

theorem valid18_516 : thresholds18_516.all (checked ⟨10,5,1⟩)=true :=
  checkedVerified ⟨10,5,1⟩ prefixMap18 thresholds18_516 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand18Part005

section Pack_Z6970H2307PackedBand19Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid19_0_0 : (thresholds19_0.take 4).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_0.take 4) (by decide +kernel)

private theorem valid19_0_4 : (thresholds19_0.drop 4).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_0.drop 4) (by decide +kernel)

theorem valid19_0 : thresholds19_0.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_0 4 valid19_0_0 (valid19_0_4)

theorem valid19_6 : thresholds19_6.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_6 (by decide +kernel)

theorem valid19_12 : thresholds19_12.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_12 (by decide +kernel)

theorem valid19_18 : thresholds19_18.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_18 (by decide +kernel)

theorem valid19_24 : thresholds19_24.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_24 (by decide +kernel)

theorem valid19_30 : thresholds19_30.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_30 (by decide +kernel)

private theorem valid19_36_0 : (thresholds19_36.take 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_36.take 5) (by decide +kernel)

private theorem valid19_36_5 : (thresholds19_36.drop 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_36.drop 5) (by decide +kernel)

theorem valid19_36 : thresholds19_36.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_36 5 valid19_36_0 (valid19_36_5)

private theorem valid19_42_0 : (thresholds19_42.take 4).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_42.take 4) (by decide +kernel)

private theorem valid19_42_4 : (thresholds19_42.drop 4).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_42.drop 4) (by decide +kernel)

theorem valid19_42 : thresholds19_42.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_42 4 valid19_42_0 (valid19_42_4)

theorem valid19_48 : thresholds19_48.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_48 (by decide +kernel)

theorem valid19_54 : thresholds19_54.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_54 (by decide +kernel)

private theorem valid19_60_0 : (thresholds19_60.take 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_60.take 5) (by decide +kernel)

private theorem valid19_60_5 : (thresholds19_60.drop 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_60.drop 5) (by decide +kernel)

theorem valid19_60 : thresholds19_60.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_60 5 valid19_60_0 (valid19_60_5)

private theorem valid19_66_0 : (thresholds19_66.take 4).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_66.take 4) (by decide +kernel)

private theorem valid19_66_4 : (thresholds19_66.drop 4).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_66.drop 4) (by decide +kernel)

theorem valid19_66 : thresholds19_66.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_66 4 valid19_66_0 (valid19_66_4)

theorem valid19_72 : thresholds19_72.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_72 (by decide +kernel)

private theorem valid19_78_0 : (thresholds19_78.take 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_78.take 5) (by decide +kernel)

private theorem valid19_78_5 : (thresholds19_78.drop 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_78.drop 5) (by decide +kernel)

theorem valid19_78 : thresholds19_78.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_78 5 valid19_78_0 (valid19_78_5)

theorem valid19_84 : thresholds19_84.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_84 (by decide +kernel)

private theorem valid19_90_0 : (thresholds19_90.take 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_90.take 5) (by decide +kernel)

private theorem valid19_90_5 : (thresholds19_90.drop 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_90.drop 5) (by decide +kernel)

theorem valid19_90 : thresholds19_90.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_90 5 valid19_90_0 (valid19_90_5)

theorem valid19_96 : thresholds19_96.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_96 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand19Part000

section Pack_Z6970H2307PackedBand19Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid19_102_0 : (thresholds19_102.take 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_102.take 5) (by decide +kernel)

private theorem valid19_102_5 : (thresholds19_102.drop 5).all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 (thresholds19_102.drop 5) (by decide +kernel)

theorem valid19_102 : thresholds19_102.all (checked ⟨17,5,1⟩)=true :=
  all_take_drop (checked ⟨17,5,1⟩) thresholds19_102 5 valid19_102_0 (valid19_102_5)

theorem valid19_108 : thresholds19_108.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_108 (by decide +kernel)

theorem valid19_114 : thresholds19_114.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_114 (by decide +kernel)

theorem valid19_120 : thresholds19_120.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_120 (by decide +kernel)

theorem valid19_126 : thresholds19_126.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_126 (by decide +kernel)

theorem valid19_132 : thresholds19_132.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_132 (by decide +kernel)

theorem valid19_138 : thresholds19_138.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_138 (by decide +kernel)

theorem valid19_144 : thresholds19_144.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_144 (by decide +kernel)

theorem valid19_150 : thresholds19_150.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_150 (by decide +kernel)

theorem valid19_156 : thresholds19_156.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_156 (by decide +kernel)

theorem valid19_162 : thresholds19_162.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_162 (by decide +kernel)

theorem valid19_168 : thresholds19_168.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_168 (by decide +kernel)

theorem valid19_174 : thresholds19_174.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_174 (by decide +kernel)

theorem valid19_180 : thresholds19_180.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_180 (by decide +kernel)

theorem valid19_186 : thresholds19_186.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_186 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand19Part001

section Pack_Z6970H2307PackedBand19Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid19_192 : thresholds19_192.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_192 (by decide +kernel)

theorem valid19_198 : thresholds19_198.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_198 (by decide +kernel)

theorem valid19_204 : thresholds19_204.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_204 (by decide +kernel)

theorem valid19_210 : thresholds19_210.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_210 (by decide +kernel)

theorem valid19_216 : thresholds19_216.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_216 (by decide +kernel)

theorem valid19_222 : thresholds19_222.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_222 (by decide +kernel)

theorem valid19_228 : thresholds19_228.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_228 (by decide +kernel)

theorem valid19_234 : thresholds19_234.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_234 (by decide +kernel)

theorem valid19_240 : thresholds19_240.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_240 (by decide +kernel)

theorem valid19_246 : thresholds19_246.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_246 (by decide +kernel)

theorem valid19_252 : thresholds19_252.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_252 (by decide +kernel)

theorem valid19_258 : thresholds19_258.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_258 (by decide +kernel)

theorem valid19_264 : thresholds19_264.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_264 (by decide +kernel)

theorem valid19_270 : thresholds19_270.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_270 (by decide +kernel)

theorem valid19_276 : thresholds19_276.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_276 (by decide +kernel)

theorem valid19_282 : thresholds19_282.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_282 (by decide +kernel)

theorem valid19_288 : thresholds19_288.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_288 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand19Part002

section Pack_Z6970H2307PackedBand19Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid19_294 : thresholds19_294.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_294 (by decide +kernel)

theorem valid19_300 : thresholds19_300.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_300 (by decide +kernel)

theorem valid19_306 : thresholds19_306.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_306 (by decide +kernel)

theorem valid19_312 : thresholds19_312.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_312 (by decide +kernel)

theorem valid19_318 : thresholds19_318.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_318 (by decide +kernel)

theorem valid19_324 : thresholds19_324.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_324 (by decide +kernel)

theorem valid19_330 : thresholds19_330.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_330 (by decide +kernel)

theorem valid19_336 : thresholds19_336.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_336 (by decide +kernel)

theorem valid19_342 : thresholds19_342.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_342 (by decide +kernel)

theorem valid19_348 : thresholds19_348.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_348 (by decide +kernel)

theorem valid19_354 : thresholds19_354.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_354 (by decide +kernel)

theorem valid19_360 : thresholds19_360.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_360 (by decide +kernel)

theorem valid19_366 : thresholds19_366.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_366 (by decide +kernel)

theorem valid19_372 : thresholds19_372.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_372 (by decide +kernel)

theorem valid19_378 : thresholds19_378.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_378 (by decide +kernel)

theorem valid19_384 : thresholds19_384.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_384 (by decide +kernel)

theorem valid19_390 : thresholds19_390.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_390 (by decide +kernel)

theorem valid19_396 : thresholds19_396.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_396 (by decide +kernel)

theorem valid19_402 : thresholds19_402.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_402 (by decide +kernel)

theorem valid19_408 : thresholds19_408.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_408 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand19Part003

section Pack_Z6970H2307PackedBand19Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid19_414 : thresholds19_414.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_414 (by decide +kernel)

theorem valid19_420 : thresholds19_420.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_420 (by decide +kernel)

theorem valid19_426 : thresholds19_426.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_426 (by decide +kernel)

theorem valid19_432 : thresholds19_432.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_432 (by decide +kernel)

theorem valid19_438 : thresholds19_438.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_438 (by decide +kernel)

theorem valid19_444 : thresholds19_444.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_444 (by decide +kernel)

theorem valid19_450 : thresholds19_450.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_450 (by decide +kernel)

theorem valid19_456 : thresholds19_456.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_456 (by decide +kernel)

theorem valid19_462 : thresholds19_462.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_462 (by decide +kernel)

theorem valid19_468 : thresholds19_468.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_468 (by decide +kernel)

theorem valid19_474 : thresholds19_474.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_474 (by decide +kernel)

theorem valid19_480 : thresholds19_480.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_480 (by decide +kernel)

theorem valid19_486 : thresholds19_486.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_486 (by decide +kernel)

theorem valid19_492 : thresholds19_492.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_492 (by decide +kernel)

theorem valid19_498 : thresholds19_498.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_498 (by decide +kernel)

theorem valid19_504 : thresholds19_504.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_504 (by decide +kernel)

theorem valid19_510 : thresholds19_510.all (checked ⟨17,5,1⟩)=true :=
  checkedVerified ⟨17,5,1⟩ prefixMap19 thresholds19_510 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand19Part004

section Pack_Z6970H2307PackedBand20Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid20_0_0 : (thresholds20_0.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_0.take 4) (by decide +kernel)

private theorem valid20_0_4 : (thresholds20_0.drop 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_0.drop 4) (by decide +kernel)

theorem valid20_0 : thresholds20_0.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_0 4 valid20_0_0 (valid20_0_4)

theorem valid20_6 : thresholds20_6.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_6 (by decide +kernel)

theorem valid20_12 : thresholds20_12.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_12 (by decide +kernel)

theorem valid20_18 : thresholds20_18.all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 thresholds20_18 (by decide +kernel)

private theorem valid20_24_0 : (thresholds20_24.take 4).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_24.take 4) (by decide +kernel)

private theorem valid20_24_4 : ((thresholds20_24.drop 4).take 1).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 ((thresholds20_24.drop 4).take 1) (by decide +kernel)

private theorem valid20_24_5 : (thresholds20_24.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_24.drop 5) (by decide +kernel)

theorem valid20_24 : thresholds20_24.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_24 4 valid20_24_0 (all_take_drop (checked ⟨2,6,1⟩) (thresholds20_24.drop 4) 1 valid20_24_4 (valid20_24_5))

private theorem valid20_30_0 : (thresholds20_30.take 3).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_30.take 3) (by decide +kernel)

private theorem valid20_30_3 : ((thresholds20_30.drop 3).take 2).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 ((thresholds20_30.drop 3).take 2) (by decide +kernel)

private theorem valid20_30_5 : (thresholds20_30.drop 5).all (checked ⟨2,6,1⟩)=true :=
  checkedVerified ⟨2,6,1⟩ prefixMap20 (thresholds20_30.drop 5) (by decide +kernel)

theorem valid20_30 : thresholds20_30.all (checked ⟨2,6,1⟩)=true :=
  all_take_drop (checked ⟨2,6,1⟩) thresholds20_30 3 valid20_30_0 (all_take_drop (checked ⟨2,6,1⟩) (thresholds20_30.drop 3) 2 valid20_30_3 (valid20_30_5))

end Height2307Orders
end Pack_Z6970H2307PackedBand20Part000
