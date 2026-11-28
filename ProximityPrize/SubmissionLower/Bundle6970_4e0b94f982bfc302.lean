import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a

section Pack_Z6970H2307PackedBand00Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_0_0 : (thresholds0_0.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_0) (thresholds0_0.take 4) (zeroPrefix_good thresholds0_0) (by decide +kernel)

private theorem valid0_0_4 : (thresholds0_0.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_0) (thresholds0_0.drop 4) (zeroPrefix_good thresholds0_0) (by decide +kernel)

theorem valid0_0 : thresholds0_0.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_0 4 valid0_0_0 (valid0_0_4)

theorem valid0_6 : thresholds0_6.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_6) thresholds0_6 (zeroPrefix_good thresholds0_6) (by decide +kernel)

theorem valid0_12 : thresholds0_12.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_12) thresholds0_12 (zeroPrefix_good thresholds0_12) (by decide +kernel)

theorem valid0_18 : thresholds0_18.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_18) thresholds0_18 (zeroPrefix_good thresholds0_18) (by decide +kernel)

private theorem valid0_24_0 : (thresholds0_24.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_24) (thresholds0_24.take 3) (zeroPrefix_good thresholds0_24) (by decide +kernel)

private theorem valid0_24_3 : (thresholds0_24.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_24) (thresholds0_24.drop 3) (zeroPrefix_good thresholds0_24) (by decide +kernel)

theorem valid0_24 : thresholds0_24.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_24 3 valid0_24_0 (valid0_24_3)

private theorem valid0_30_0 : (thresholds0_30.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_30) (thresholds0_30.take 4) (zeroPrefix_good thresholds0_30) (by decide +kernel)

private theorem valid0_30_4 : (thresholds0_30.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_30) (thresholds0_30.drop 4) (zeroPrefix_good thresholds0_30) (by decide +kernel)

theorem valid0_30 : thresholds0_30.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_30 4 valid0_30_0 (valid0_30_4)

private theorem valid0_36_0 : (thresholds0_36.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_36) (thresholds0_36.take 5) (zeroPrefix_good thresholds0_36) (by decide +kernel)

private theorem valid0_36_5 : (thresholds0_36.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_36) (thresholds0_36.drop 5) (zeroPrefix_good thresholds0_36) (by decide +kernel)

theorem valid0_36 : thresholds0_36.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_36 5 valid0_36_0 (valid0_36_5)

private theorem valid0_42_0 : (thresholds0_42.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_42) (thresholds0_42.take 4) (zeroPrefix_good thresholds0_42) (by decide +kernel)

private theorem valid0_42_4 : (thresholds0_42.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_42) (thresholds0_42.drop 4) (zeroPrefix_good thresholds0_42) (by decide +kernel)

theorem valid0_42 : thresholds0_42.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_42 4 valid0_42_0 (valid0_42_4)

theorem valid0_48 : thresholds0_48.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_48) thresholds0_48 (zeroPrefix_good thresholds0_48) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part000

section Pack_Z6970H2307PackedBand00Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_54_0 : (thresholds0_54.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_54) (thresholds0_54.take 5) (zeroPrefix_good thresholds0_54) (by decide +kernel)

private theorem valid0_54_5 : (thresholds0_54.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_54) (thresholds0_54.drop 5) (zeroPrefix_good thresholds0_54) (by decide +kernel)

theorem valid0_54 : thresholds0_54.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_54 5 valid0_54_0 (valid0_54_5)

private theorem valid0_60_0 : (thresholds0_60.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_60) (thresholds0_60.take 3) (zeroPrefix_good thresholds0_60) (by decide +kernel)

private theorem valid0_60_3 : (thresholds0_60.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_60) (thresholds0_60.drop 3) (zeroPrefix_good thresholds0_60) (by decide +kernel)

theorem valid0_60 : thresholds0_60.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_60 3 valid0_60_0 (valid0_60_3)

private theorem valid0_66_0 : (thresholds0_66.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_66) (thresholds0_66.take 5) (zeroPrefix_good thresholds0_66) (by decide +kernel)

private theorem valid0_66_5 : (thresholds0_66.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_66) (thresholds0_66.drop 5) (zeroPrefix_good thresholds0_66) (by decide +kernel)

theorem valid0_66 : thresholds0_66.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_66 5 valid0_66_0 (valid0_66_5)

theorem valid0_72 : thresholds0_72.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_72) thresholds0_72 (zeroPrefix_good thresholds0_72) (by decide +kernel)

theorem valid0_78 : thresholds0_78.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_78) thresholds0_78 (zeroPrefix_good thresholds0_78) (by decide +kernel)

private theorem valid0_84_0 : (thresholds0_84.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_84) (thresholds0_84.take 5) (zeroPrefix_good thresholds0_84) (by decide +kernel)

private theorem valid0_84_5 : (thresholds0_84.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_84) (thresholds0_84.drop 5) (zeroPrefix_good thresholds0_84) (by decide +kernel)

theorem valid0_84 : thresholds0_84.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_84 5 valid0_84_0 (valid0_84_5)

private theorem valid0_90_0 : (thresholds0_90.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_90) (thresholds0_90.take 4) (zeroPrefix_good thresholds0_90) (by decide +kernel)

private theorem valid0_90_4 : (thresholds0_90.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_90) (thresholds0_90.drop 4) (zeroPrefix_good thresholds0_90) (by decide +kernel)

theorem valid0_90 : thresholds0_90.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_90 4 valid0_90_0 (valid0_90_4)

private theorem valid0_96_0 : (thresholds0_96.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_96) (thresholds0_96.take 5) (zeroPrefix_good thresholds0_96) (by decide +kernel)

private theorem valid0_96_5 : (thresholds0_96.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_96) (thresholds0_96.drop 5) (zeroPrefix_good thresholds0_96) (by decide +kernel)

theorem valid0_96 : thresholds0_96.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_96 5 valid0_96_0 (valid0_96_5)

private theorem valid0_102_0 : (thresholds0_102.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_102) (thresholds0_102.take 4) (zeroPrefix_good thresholds0_102) (by decide +kernel)

private theorem valid0_102_4 : (thresholds0_102.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_102) (thresholds0_102.drop 4) (zeroPrefix_good thresholds0_102) (by decide +kernel)

theorem valid0_102 : thresholds0_102.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_102 4 valid0_102_0 (valid0_102_4)

private theorem valid0_108_0 : (thresholds0_108.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_108) (thresholds0_108.take 5) (zeroPrefix_good thresholds0_108) (by decide +kernel)

private theorem valid0_108_5 : (thresholds0_108.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_108) (thresholds0_108.drop 5) (zeroPrefix_good thresholds0_108) (by decide +kernel)

theorem valid0_108 : thresholds0_108.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_108 5 valid0_108_0 (valid0_108_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part001

section Pack_Z6970H2307PackedBand00Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_114_0 : (thresholds0_114.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_114) (thresholds0_114.take 4) (zeroPrefix_good thresholds0_114) (by decide +kernel)

private theorem valid0_114_4 : (thresholds0_114.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_114) (thresholds0_114.drop 4) (zeroPrefix_good thresholds0_114) (by decide +kernel)

theorem valid0_114 : thresholds0_114.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_114 4 valid0_114_0 (valid0_114_4)

private theorem valid0_120_0 : (thresholds0_120.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_120) (thresholds0_120.take 4) (zeroPrefix_good thresholds0_120) (by decide +kernel)

private theorem valid0_120_4 : (thresholds0_120.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_120) (thresholds0_120.drop 4) (zeroPrefix_good thresholds0_120) (by decide +kernel)

theorem valid0_120 : thresholds0_120.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_120 4 valid0_120_0 (valid0_120_4)

private theorem valid0_126_0 : (thresholds0_126.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_126) (thresholds0_126.take 5) (zeroPrefix_good thresholds0_126) (by decide +kernel)

private theorem valid0_126_5 : (thresholds0_126.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_126) (thresholds0_126.drop 5) (zeroPrefix_good thresholds0_126) (by decide +kernel)

theorem valid0_126 : thresholds0_126.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_126 5 valid0_126_0 (valid0_126_5)

private theorem valid0_132_0 : (thresholds0_132.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_132) (thresholds0_132.take 5) (zeroPrefix_good thresholds0_132) (by decide +kernel)

private theorem valid0_132_5 : (thresholds0_132.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_132) (thresholds0_132.drop 5) (zeroPrefix_good thresholds0_132) (by decide +kernel)

theorem valid0_132 : thresholds0_132.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_132 5 valid0_132_0 (valid0_132_5)

private theorem valid0_138_0 : (thresholds0_138.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_138) (thresholds0_138.take 4) (zeroPrefix_good thresholds0_138) (by decide +kernel)

private theorem valid0_138_4 : (thresholds0_138.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_138) (thresholds0_138.drop 4) (zeroPrefix_good thresholds0_138) (by decide +kernel)

theorem valid0_138 : thresholds0_138.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_138 4 valid0_138_0 (valid0_138_4)

private theorem valid0_144_0 : (thresholds0_144.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_144) (thresholds0_144.take 5) (zeroPrefix_good thresholds0_144) (by decide +kernel)

private theorem valid0_144_5 : (thresholds0_144.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_144) (thresholds0_144.drop 5) (zeroPrefix_good thresholds0_144) (by decide +kernel)

theorem valid0_144 : thresholds0_144.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_144 5 valid0_144_0 (valid0_144_5)

private theorem valid0_150_0 : (thresholds0_150.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_150) (thresholds0_150.take 3) (zeroPrefix_good thresholds0_150) (by decide +kernel)

private theorem valid0_150_3 : (thresholds0_150.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_150) (thresholds0_150.drop 3) (zeroPrefix_good thresholds0_150) (by decide +kernel)

theorem valid0_150 : thresholds0_150.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_150 3 valid0_150_0 (valid0_150_3)

private theorem valid0_156_0 : (thresholds0_156.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_156) (thresholds0_156.take 4) (zeroPrefix_good thresholds0_156) (by decide +kernel)

private theorem valid0_156_4 : (thresholds0_156.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_156) (thresholds0_156.drop 4) (zeroPrefix_good thresholds0_156) (by decide +kernel)

theorem valid0_156 : thresholds0_156.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_156 4 valid0_156_0 (valid0_156_4)

theorem valid0_162 : thresholds0_162.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_162) thresholds0_162 (zeroPrefix_good thresholds0_162) (by decide +kernel)

private theorem valid0_168_0 : (thresholds0_168.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_168) (thresholds0_168.take 3) (zeroPrefix_good thresholds0_168) (by decide +kernel)

private theorem valid0_168_3 : (thresholds0_168.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_168) (thresholds0_168.drop 3) (zeroPrefix_good thresholds0_168) (by decide +kernel)

theorem valid0_168 : thresholds0_168.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_168 3 valid0_168_0 (valid0_168_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part002

section Pack_Z6970H2307PackedBand00Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_174_0 : (thresholds0_174.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_174) (thresholds0_174.take 5) (zeroPrefix_good thresholds0_174) (by decide +kernel)

private theorem valid0_174_5 : (thresholds0_174.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_174) (thresholds0_174.drop 5) (zeroPrefix_good thresholds0_174) (by decide +kernel)

theorem valid0_174 : thresholds0_174.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_174 5 valid0_174_0 (valid0_174_5)

private theorem valid0_180_0 : (thresholds0_180.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_180) (thresholds0_180.take 3) (zeroPrefix_good thresholds0_180) (by decide +kernel)

private theorem valid0_180_3 : (thresholds0_180.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_180) (thresholds0_180.drop 3) (zeroPrefix_good thresholds0_180) (by decide +kernel)

theorem valid0_180 : thresholds0_180.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_180 3 valid0_180_0 (valid0_180_3)

private theorem valid0_186_0 : (thresholds0_186.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_186) (thresholds0_186.take 3) (zeroPrefix_good thresholds0_186) (by decide +kernel)

private theorem valid0_186_3 : (thresholds0_186.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_186) (thresholds0_186.drop 3) (zeroPrefix_good thresholds0_186) (by decide +kernel)

theorem valid0_186 : thresholds0_186.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_186 3 valid0_186_0 (valid0_186_3)

private theorem valid0_192_0 : (thresholds0_192.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_192) (thresholds0_192.take 4) (zeroPrefix_good thresholds0_192) (by decide +kernel)

private theorem valid0_192_4 : (thresholds0_192.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_192) (thresholds0_192.drop 4) (zeroPrefix_good thresholds0_192) (by decide +kernel)

theorem valid0_192 : thresholds0_192.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_192 4 valid0_192_0 (valid0_192_4)

private theorem valid0_198_0 : (thresholds0_198.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_198) (thresholds0_198.take 3) (zeroPrefix_good thresholds0_198) (by decide +kernel)

private theorem valid0_198_3 : (thresholds0_198.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_198) (thresholds0_198.drop 3) (zeroPrefix_good thresholds0_198) (by decide +kernel)

theorem valid0_198 : thresholds0_198.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_198 3 valid0_198_0 (valid0_198_3)

private theorem valid0_204_0 : (thresholds0_204.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_204) (thresholds0_204.take 3) (zeroPrefix_good thresholds0_204) (by decide +kernel)

private theorem valid0_204_3 : (thresholds0_204.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_204) (thresholds0_204.drop 3) (zeroPrefix_good thresholds0_204) (by decide +kernel)

theorem valid0_204 : thresholds0_204.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_204 3 valid0_204_0 (valid0_204_3)

private theorem valid0_210_0 : (thresholds0_210.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_210) (thresholds0_210.take 5) (zeroPrefix_good thresholds0_210) (by decide +kernel)

private theorem valid0_210_5 : (thresholds0_210.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_210) (thresholds0_210.drop 5) (zeroPrefix_good thresholds0_210) (by decide +kernel)

theorem valid0_210 : thresholds0_210.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_210 5 valid0_210_0 (valid0_210_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part003

section Pack_Z6970H2307PackedBand00Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_216_0 : (thresholds0_216.take 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_216) (thresholds0_216.take 2) (zeroPrefix_good thresholds0_216) (by decide +kernel)

private theorem valid0_216_2 : (thresholds0_216.drop 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_216) (thresholds0_216.drop 2) (zeroPrefix_good thresholds0_216) (by decide +kernel)

theorem valid0_216 : thresholds0_216.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_216 2 valid0_216_0 (valid0_216_2)

private theorem valid0_222_0 : (thresholds0_222.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_222) (thresholds0_222.take 4) (zeroPrefix_good thresholds0_222) (by decide +kernel)

private theorem valid0_222_4 : (thresholds0_222.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_222) (thresholds0_222.drop 4) (zeroPrefix_good thresholds0_222) (by decide +kernel)

theorem valid0_222 : thresholds0_222.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_222 4 valid0_222_0 (valid0_222_4)

theorem valid0_228 : thresholds0_228.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_228) thresholds0_228 (zeroPrefix_good thresholds0_228) (by decide +kernel)

private theorem valid0_234_0 : (thresholds0_234.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_234) (thresholds0_234.take 3) (zeroPrefix_good thresholds0_234) (by decide +kernel)

private theorem valid0_234_3 : (thresholds0_234.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_234) (thresholds0_234.drop 3) (zeroPrefix_good thresholds0_234) (by decide +kernel)

theorem valid0_234 : thresholds0_234.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_234 3 valid0_234_0 (valid0_234_3)

private theorem valid0_240_0 : (thresholds0_240.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_240) (thresholds0_240.take 5) (zeroPrefix_good thresholds0_240) (by decide +kernel)

private theorem valid0_240_5 : (thresholds0_240.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_240) (thresholds0_240.drop 5) (zeroPrefix_good thresholds0_240) (by decide +kernel)

theorem valid0_240 : thresholds0_240.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_240 5 valid0_240_0 (valid0_240_5)

private theorem valid0_246_0 : (thresholds0_246.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_246) (thresholds0_246.take 3) (zeroPrefix_good thresholds0_246) (by decide +kernel)

private theorem valid0_246_3 : (thresholds0_246.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_246) (thresholds0_246.drop 3) (zeroPrefix_good thresholds0_246) (by decide +kernel)

theorem valid0_246 : thresholds0_246.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_246 3 valid0_246_0 (valid0_246_3)

private theorem valid0_252_0 : (thresholds0_252.take 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_252) (thresholds0_252.take 2) (zeroPrefix_good thresholds0_252) (by decide +kernel)

private theorem valid0_252_2 : ((thresholds0_252.drop 2).take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_252) ((thresholds0_252.drop 2).take 3) (zeroPrefix_good thresholds0_252) (by decide +kernel)

private theorem valid0_252_5 : (thresholds0_252.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_252) (thresholds0_252.drop 5) (zeroPrefix_good thresholds0_252) (by decide +kernel)

theorem valid0_252 : thresholds0_252.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_252 2 valid0_252_0 (all_take_drop (checked ⟨0,0,0⟩) (thresholds0_252.drop 2) 3 valid0_252_2 (valid0_252_5))

private theorem valid0_258_0 : (thresholds0_258.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_258) (thresholds0_258.take 4) (zeroPrefix_good thresholds0_258) (by decide +kernel)

private theorem valid0_258_4 : (thresholds0_258.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_258) (thresholds0_258.drop 4) (zeroPrefix_good thresholds0_258) (by decide +kernel)

theorem valid0_258 : thresholds0_258.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_258 4 valid0_258_0 (valid0_258_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part004

section Pack_Z6970H2307PackedBand00Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_264_0 : (thresholds0_264.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_264) (thresholds0_264.take 4) (zeroPrefix_good thresholds0_264) (by decide +kernel)

private theorem valid0_264_4 : (thresholds0_264.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_264) (thresholds0_264.drop 4) (zeroPrefix_good thresholds0_264) (by decide +kernel)

theorem valid0_264 : thresholds0_264.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_264 4 valid0_264_0 (valid0_264_4)

private theorem valid0_270_0 : (thresholds0_270.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_270) (thresholds0_270.take 4) (zeroPrefix_good thresholds0_270) (by decide +kernel)

private theorem valid0_270_4 : (thresholds0_270.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_270) (thresholds0_270.drop 4) (zeroPrefix_good thresholds0_270) (by decide +kernel)

theorem valid0_270 : thresholds0_270.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_270 4 valid0_270_0 (valid0_270_4)

private theorem valid0_276_0 : (thresholds0_276.take 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_276) (thresholds0_276.take 2) (zeroPrefix_good thresholds0_276) (by decide +kernel)

private theorem valid0_276_2 : (thresholds0_276.drop 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_276) (thresholds0_276.drop 2) (zeroPrefix_good thresholds0_276) (by decide +kernel)

theorem valid0_276 : thresholds0_276.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_276 2 valid0_276_0 (valid0_276_2)

private theorem valid0_282_0 : (thresholds0_282.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_282) (thresholds0_282.take 4) (zeroPrefix_good thresholds0_282) (by decide +kernel)

private theorem valid0_282_4 : (thresholds0_282.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_282) (thresholds0_282.drop 4) (zeroPrefix_good thresholds0_282) (by decide +kernel)

theorem valid0_282 : thresholds0_282.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_282 4 valid0_282_0 (valid0_282_4)

theorem valid0_288 : thresholds0_288.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_288) thresholds0_288 (zeroPrefix_good thresholds0_288) (by decide +kernel)

private theorem valid0_294_0 : (thresholds0_294.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_294) (thresholds0_294.take 4) (zeroPrefix_good thresholds0_294) (by decide +kernel)

private theorem valid0_294_4 : (thresholds0_294.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_294) (thresholds0_294.drop 4) (zeroPrefix_good thresholds0_294) (by decide +kernel)

theorem valid0_294 : thresholds0_294.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_294 4 valid0_294_0 (valid0_294_4)

private theorem valid0_300_0 : (thresholds0_300.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_300) (thresholds0_300.take 3) (zeroPrefix_good thresholds0_300) (by decide +kernel)

private theorem valid0_300_3 : (thresholds0_300.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_300) (thresholds0_300.drop 3) (zeroPrefix_good thresholds0_300) (by decide +kernel)

theorem valid0_300 : thresholds0_300.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_300 3 valid0_300_0 (valid0_300_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part005

section Pack_Z6970H2307PackedBand00Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_306_0 : (thresholds0_306.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_306) (thresholds0_306.take 5) (zeroPrefix_good thresholds0_306) (by decide +kernel)

private theorem valid0_306_5 : (thresholds0_306.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_306) (thresholds0_306.drop 5) (zeroPrefix_good thresholds0_306) (by decide +kernel)

theorem valid0_306 : thresholds0_306.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_306 5 valid0_306_0 (valid0_306_5)

theorem valid0_312 : thresholds0_312.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_312) thresholds0_312 (zeroPrefix_good thresholds0_312) (by decide +kernel)

private theorem valid0_318_0 : (thresholds0_318.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_318) (thresholds0_318.take 3) (zeroPrefix_good thresholds0_318) (by decide +kernel)

private theorem valid0_318_3 : (thresholds0_318.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_318) (thresholds0_318.drop 3) (zeroPrefix_good thresholds0_318) (by decide +kernel)

theorem valid0_318 : thresholds0_318.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_318 3 valid0_318_0 (valid0_318_3)

private theorem valid0_324_0 : (thresholds0_324.take 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_324) (thresholds0_324.take 2) (zeroPrefix_good thresholds0_324) (by decide +kernel)

private theorem valid0_324_2 : (thresholds0_324.drop 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_324) (thresholds0_324.drop 2) (zeroPrefix_good thresholds0_324) (by decide +kernel)

theorem valid0_324 : thresholds0_324.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_324 2 valid0_324_0 (valid0_324_2)

private theorem valid0_330_0 : (thresholds0_330.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_330) (thresholds0_330.take 4) (zeroPrefix_good thresholds0_330) (by decide +kernel)

private theorem valid0_330_4 : (thresholds0_330.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_330) (thresholds0_330.drop 4) (zeroPrefix_good thresholds0_330) (by decide +kernel)

theorem valid0_330 : thresholds0_330.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_330 4 valid0_330_0 (valid0_330_4)

private theorem valid0_336_0 : (thresholds0_336.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_336) (thresholds0_336.take 5) (zeroPrefix_good thresholds0_336) (by decide +kernel)

private theorem valid0_336_5 : (thresholds0_336.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_336) (thresholds0_336.drop 5) (zeroPrefix_good thresholds0_336) (by decide +kernel)

theorem valid0_336 : thresholds0_336.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_336 5 valid0_336_0 (valid0_336_5)

private theorem valid0_342_0 : (thresholds0_342.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_342) (thresholds0_342.take 3) (zeroPrefix_good thresholds0_342) (by decide +kernel)

private theorem valid0_342_3 : ((thresholds0_342.drop 3).take 2).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_342) ((thresholds0_342.drop 3).take 2) (zeroPrefix_good thresholds0_342) (by decide +kernel)

private theorem valid0_342_5 : (thresholds0_342.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_342) (thresholds0_342.drop 5) (zeroPrefix_good thresholds0_342) (by decide +kernel)

theorem valid0_342 : thresholds0_342.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_342 3 valid0_342_0 (all_take_drop (checked ⟨0,0,0⟩) (thresholds0_342.drop 3) 2 valid0_342_3 (valid0_342_5))

theorem valid0_348 : thresholds0_348.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_348) thresholds0_348 (zeroPrefix_good thresholds0_348) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part006

section Pack_Z6970H2307PackedBand00Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_354_0 : (thresholds0_354.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_354) (thresholds0_354.take 5) (zeroPrefix_good thresholds0_354) (by decide +kernel)

private theorem valid0_354_5 : (thresholds0_354.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_354) (thresholds0_354.drop 5) (zeroPrefix_good thresholds0_354) (by decide +kernel)

theorem valid0_354 : thresholds0_354.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_354 5 valid0_354_0 (valid0_354_5)

private theorem valid0_360_0 : (thresholds0_360.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_360) (thresholds0_360.take 4) (zeroPrefix_good thresholds0_360) (by decide +kernel)

private theorem valid0_360_4 : (thresholds0_360.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_360) (thresholds0_360.drop 4) (zeroPrefix_good thresholds0_360) (by decide +kernel)

theorem valid0_360 : thresholds0_360.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_360 4 valid0_360_0 (valid0_360_4)

theorem valid0_366 : thresholds0_366.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_366) thresholds0_366 (zeroPrefix_good thresholds0_366) (by decide +kernel)

private theorem valid0_372_0 : (thresholds0_372.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_372) (thresholds0_372.take 4) (zeroPrefix_good thresholds0_372) (by decide +kernel)

private theorem valid0_372_4 : (thresholds0_372.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_372) (thresholds0_372.drop 4) (zeroPrefix_good thresholds0_372) (by decide +kernel)

theorem valid0_372 : thresholds0_372.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_372 4 valid0_372_0 (valid0_372_4)

private theorem valid0_378_0 : (thresholds0_378.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_378) (thresholds0_378.take 4) (zeroPrefix_good thresholds0_378) (by decide +kernel)

private theorem valid0_378_4 : (thresholds0_378.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_378) (thresholds0_378.drop 4) (zeroPrefix_good thresholds0_378) (by decide +kernel)

theorem valid0_378 : thresholds0_378.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_378 4 valid0_378_0 (valid0_378_4)

private theorem valid0_384_0 : (thresholds0_384.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_384) (thresholds0_384.take 4) (zeroPrefix_good thresholds0_384) (by decide +kernel)

private theorem valid0_384_4 : (thresholds0_384.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_384) (thresholds0_384.drop 4) (zeroPrefix_good thresholds0_384) (by decide +kernel)

theorem valid0_384 : thresholds0_384.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_384 4 valid0_384_0 (valid0_384_4)

private theorem valid0_390_0 : (thresholds0_390.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_390) (thresholds0_390.take 5) (zeroPrefix_good thresholds0_390) (by decide +kernel)

private theorem valid0_390_5 : (thresholds0_390.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_390) (thresholds0_390.drop 5) (zeroPrefix_good thresholds0_390) (by decide +kernel)

theorem valid0_390 : thresholds0_390.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_390 5 valid0_390_0 (valid0_390_5)

private theorem valid0_396_0 : (thresholds0_396.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_396) (thresholds0_396.take 3) (zeroPrefix_good thresholds0_396) (by decide +kernel)

private theorem valid0_396_3 : (thresholds0_396.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_396) (thresholds0_396.drop 3) (zeroPrefix_good thresholds0_396) (by decide +kernel)

theorem valid0_396 : thresholds0_396.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_396 3 valid0_396_0 (valid0_396_3)

theorem valid0_402 : thresholds0_402.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_402) thresholds0_402 (zeroPrefix_good thresholds0_402) (by decide +kernel)

theorem valid0_408 : thresholds0_408.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_408) thresholds0_408 (zeroPrefix_good thresholds0_408) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part007

section Pack_Z6970H2307PackedBand00Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_414_0 : (thresholds0_414.take 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_414) (thresholds0_414.take 3) (zeroPrefix_good thresholds0_414) (by decide +kernel)

private theorem valid0_414_3 : (thresholds0_414.drop 3).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_414) (thresholds0_414.drop 3) (zeroPrefix_good thresholds0_414) (by decide +kernel)

theorem valid0_414 : thresholds0_414.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_414 3 valid0_414_0 (valid0_414_3)

private theorem valid0_420_0 : (thresholds0_420.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_420) (thresholds0_420.take 5) (zeroPrefix_good thresholds0_420) (by decide +kernel)

private theorem valid0_420_5 : (thresholds0_420.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_420) (thresholds0_420.drop 5) (zeroPrefix_good thresholds0_420) (by decide +kernel)

theorem valid0_420 : thresholds0_420.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_420 5 valid0_420_0 (valid0_420_5)

private theorem valid0_426_0 : (thresholds0_426.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_426) (thresholds0_426.take 5) (zeroPrefix_good thresholds0_426) (by decide +kernel)

private theorem valid0_426_5 : (thresholds0_426.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_426) (thresholds0_426.drop 5) (zeroPrefix_good thresholds0_426) (by decide +kernel)

theorem valid0_426 : thresholds0_426.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_426 5 valid0_426_0 (valid0_426_5)

private theorem valid0_432_0 : (thresholds0_432.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_432) (thresholds0_432.take 5) (zeroPrefix_good thresholds0_432) (by decide +kernel)

private theorem valid0_432_5 : (thresholds0_432.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_432) (thresholds0_432.drop 5) (zeroPrefix_good thresholds0_432) (by decide +kernel)

theorem valid0_432 : thresholds0_432.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_432 5 valid0_432_0 (valid0_432_5)

theorem valid0_438 : thresholds0_438.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_438) thresholds0_438 (zeroPrefix_good thresholds0_438) (by decide +kernel)

theorem valid0_444 : thresholds0_444.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_444) thresholds0_444 (zeroPrefix_good thresholds0_444) (by decide +kernel)

private theorem valid0_450_0 : (thresholds0_450.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_450) (thresholds0_450.take 4) (zeroPrefix_good thresholds0_450) (by decide +kernel)

private theorem valid0_450_4 : (thresholds0_450.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_450) (thresholds0_450.drop 4) (zeroPrefix_good thresholds0_450) (by decide +kernel)

theorem valid0_450 : thresholds0_450.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_450 4 valid0_450_0 (valid0_450_4)

private theorem valid0_456_0 : (thresholds0_456.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_456) (thresholds0_456.take 5) (zeroPrefix_good thresholds0_456) (by decide +kernel)

private theorem valid0_456_5 : (thresholds0_456.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_456) (thresholds0_456.drop 5) (zeroPrefix_good thresholds0_456) (by decide +kernel)

theorem valid0_456 : thresholds0_456.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_456 5 valid0_456_0 (valid0_456_5)

private theorem valid0_462_0 : (thresholds0_462.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_462) (thresholds0_462.take 5) (zeroPrefix_good thresholds0_462) (by decide +kernel)

private theorem valid0_462_5 : (thresholds0_462.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_462) (thresholds0_462.drop 5) (zeroPrefix_good thresholds0_462) (by decide +kernel)

theorem valid0_462 : thresholds0_462.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_462 5 valid0_462_0 (valid0_462_5)

private theorem valid0_468_0 : (thresholds0_468.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_468) (thresholds0_468.take 5) (zeroPrefix_good thresholds0_468) (by decide +kernel)

private theorem valid0_468_5 : (thresholds0_468.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_468) (thresholds0_468.drop 5) (zeroPrefix_good thresholds0_468) (by decide +kernel)

theorem valid0_468 : thresholds0_468.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_468 5 valid0_468_0 (valid0_468_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part008

section Pack_Z6970H2307PackedBand00Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid0_474 : thresholds0_474.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_474) thresholds0_474 (zeroPrefix_good thresholds0_474) (by decide +kernel)

theorem valid0_480 : thresholds0_480.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_480) thresholds0_480 (zeroPrefix_good thresholds0_480) (by decide +kernel)

theorem valid0_486 : thresholds0_486.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_486) thresholds0_486 (zeroPrefix_good thresholds0_486) (by decide +kernel)

private theorem valid0_492_0 : (thresholds0_492.take 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_492) (thresholds0_492.take 4) (zeroPrefix_good thresholds0_492) (by decide +kernel)

private theorem valid0_492_4 : (thresholds0_492.drop 4).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_492) (thresholds0_492.drop 4) (zeroPrefix_good thresholds0_492) (by decide +kernel)

theorem valid0_492 : thresholds0_492.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_492 4 valid0_492_0 (valid0_492_4)

private theorem valid0_498_0 : (thresholds0_498.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_498) (thresholds0_498.take 5) (zeroPrefix_good thresholds0_498) (by decide +kernel)

private theorem valid0_498_5 : (thresholds0_498.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_498) (thresholds0_498.drop 5) (zeroPrefix_good thresholds0_498) (by decide +kernel)

theorem valid0_498 : thresholds0_498.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_498 5 valid0_498_0 (valid0_498_5)

theorem valid0_504 : thresholds0_504.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_504) thresholds0_504 (zeroPrefix_good thresholds0_504) (by decide +kernel)

theorem valid0_510 : thresholds0_510.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_510) thresholds0_510 (zeroPrefix_good thresholds0_510) (by decide +kernel)

theorem valid0_516 : thresholds0_516.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_516) thresholds0_516 (zeroPrefix_good thresholds0_516) (by decide +kernel)

private theorem valid0_522_0 : (thresholds0_522.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_522) (thresholds0_522.take 5) (zeroPrefix_good thresholds0_522) (by decide +kernel)

private theorem valid0_522_5 : (thresholds0_522.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_522) (thresholds0_522.drop 5) (zeroPrefix_good thresholds0_522) (by decide +kernel)

theorem valid0_522 : thresholds0_522.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_522 5 valid0_522_0 (valid0_522_5)

theorem valid0_528 : thresholds0_528.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_528) thresholds0_528 (zeroPrefix_good thresholds0_528) (by decide +kernel)

theorem valid0_534 : thresholds0_534.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_534) thresholds0_534 (zeroPrefix_good thresholds0_534) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part009

section Pack_Z6970H2307PackedBand00Part010

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid0_540_0 : (thresholds0_540.take 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_540) (thresholds0_540.take 5) (zeroPrefix_good thresholds0_540) (by decide +kernel)

private theorem valid0_540_5 : (thresholds0_540.drop 5).all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_540) (thresholds0_540.drop 5) (zeroPrefix_good thresholds0_540) (by decide +kernel)

theorem valid0_540 : thresholds0_540.all (checked ⟨0,0,0⟩)=true :=
  all_take_drop (checked ⟨0,0,0⟩) thresholds0_540 5 valid0_540_0 (valid0_540_5)

theorem valid0_546 : thresholds0_546.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_546) thresholds0_546 (zeroPrefix_good thresholds0_546) (by decide +kernel)

theorem valid0_552 : thresholds0_552.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_552) thresholds0_552 (zeroPrefix_good thresholds0_552) (by decide +kernel)

theorem valid0_558 : thresholds0_558.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_558) thresholds0_558 (zeroPrefix_good thresholds0_558) (by decide +kernel)

theorem valid0_564 : thresholds0_564.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_564) thresholds0_564 (zeroPrefix_good thresholds0_564) (by decide +kernel)

theorem valid0_570 : thresholds0_570.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_570) thresholds0_570 (zeroPrefix_good thresholds0_570) (by decide +kernel)

theorem valid0_576 : thresholds0_576.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_576) thresholds0_576 (zeroPrefix_good thresholds0_576) (by decide +kernel)

theorem valid0_582 : thresholds0_582.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_582) thresholds0_582 (zeroPrefix_good thresholds0_582) (by decide +kernel)

theorem valid0_588 : thresholds0_588.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_588) thresholds0_588 (zeroPrefix_good thresholds0_588) (by decide +kernel)

theorem valid0_594 : thresholds0_594.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_594) thresholds0_594 (zeroPrefix_good thresholds0_594) (by decide +kernel)

theorem valid0_600 : thresholds0_600.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_600) thresholds0_600 (zeroPrefix_good thresholds0_600) (by decide +kernel)

theorem valid0_606 : thresholds0_606.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_606) thresholds0_606 (zeroPrefix_good thresholds0_606) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part010

section Pack_Z6970H2307PackedBand00Part011

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid0_612 : thresholds0_612.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_612) thresholds0_612 (zeroPrefix_good thresholds0_612) (by decide +kernel)

theorem valid0_618 : thresholds0_618.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_618) thresholds0_618 (zeroPrefix_good thresholds0_618) (by decide +kernel)

theorem valid0_624 : thresholds0_624.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_624) thresholds0_624 (zeroPrefix_good thresholds0_624) (by decide +kernel)

theorem valid0_630 : thresholds0_630.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_630) thresholds0_630 (zeroPrefix_good thresholds0_630) (by decide +kernel)

theorem valid0_636 : thresholds0_636.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_636) thresholds0_636 (zeroPrefix_good thresholds0_636) (by decide +kernel)

theorem valid0_642 : thresholds0_642.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_642) thresholds0_642 (zeroPrefix_good thresholds0_642) (by decide +kernel)

theorem valid0_648 : thresholds0_648.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_648) thresholds0_648 (zeroPrefix_good thresholds0_648) (by decide +kernel)

theorem valid0_654 : thresholds0_654.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_654) thresholds0_654 (zeroPrefix_good thresholds0_654) (by decide +kernel)

theorem valid0_660 : thresholds0_660.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_660) thresholds0_660 (zeroPrefix_good thresholds0_660) (by decide +kernel)

theorem valid0_666 : thresholds0_666.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_666) thresholds0_666 (zeroPrefix_good thresholds0_666) (by decide +kernel)

theorem valid0_672 : thresholds0_672.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_672) thresholds0_672 (zeroPrefix_good thresholds0_672) (by decide +kernel)

theorem valid0_678 : thresholds0_678.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_678) thresholds0_678 (zeroPrefix_good thresholds0_678) (by decide +kernel)

theorem valid0_684 : thresholds0_684.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_684) thresholds0_684 (zeroPrefix_good thresholds0_684) (by decide +kernel)

theorem valid0_690 : thresholds0_690.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_690) thresholds0_690 (zeroPrefix_good thresholds0_690) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part011

section Pack_Z6970H2307PackedBand00Part012

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid0_696 : thresholds0_696.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_696) thresholds0_696 (zeroPrefix_good thresholds0_696) (by decide +kernel)

theorem valid0_702 : thresholds0_702.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_702) thresholds0_702 (zeroPrefix_good thresholds0_702) (by decide +kernel)

theorem valid0_708 : thresholds0_708.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_708) thresholds0_708 (zeroPrefix_good thresholds0_708) (by decide +kernel)

theorem valid0_714 : thresholds0_714.all (checked ⟨0,0,0⟩)=true :=
  checkedShard ⟨0,0,0⟩ (zeroPrefix thresholds0_714) thresholds0_714 (zeroPrefix_good thresholds0_714) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand00Part012
