import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_e9774b3fc07c89e3

section Pack_Z6970H2307PackedBand01Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_0_0 : (thresholds1_0.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_0.take 4) (by decide +kernel)

private theorem valid1_0_4 : (thresholds1_0.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_0.drop 4) (by decide +kernel)

theorem valid1_0 : thresholds1_0.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_0 4 valid1_0_0 (valid1_0_4)

theorem valid1_6 : thresholds1_6.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_6 (by decide +kernel)

theorem valid1_12 : thresholds1_12.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_12 (by decide +kernel)

theorem valid1_18 : thresholds1_18.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_18 (by decide +kernel)

theorem valid1_24 : thresholds1_24.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_24 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part000

section Pack_Z6970H2307PackedBand01Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_30_0 : (thresholds1_30.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_30.take 3) (by decide +kernel)

private theorem valid1_30_3 : ((thresholds1_30.drop 3).take 2).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 ((thresholds1_30.drop 3).take 2) (by decide +kernel)

private theorem valid1_30_5 : (thresholds1_30.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_30.drop 5) (by decide +kernel)

theorem valid1_30 : thresholds1_30.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_30 3 valid1_30_0 (all_take_drop (checked ⟨1,3,1⟩) (thresholds1_30.drop 3) 2 valid1_30_3 (valid1_30_5))

private theorem valid1_36_0 : (thresholds1_36.take 1).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_36.take 1) (by decide +kernel)

private theorem valid1_36_1 : ((thresholds1_36.drop 1).take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 ((thresholds1_36.drop 1).take 4) (by decide +kernel)

private theorem valid1_36_5 : (thresholds1_36.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_36.drop 5) (by decide +kernel)

theorem valid1_36 : thresholds1_36.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_36 1 valid1_36_0 (all_take_drop (checked ⟨1,3,1⟩) (thresholds1_36.drop 1) 4 valid1_36_1 (valid1_36_5))

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part001

section Pack_Z6970H2307PackedBand01Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_42_0 : (thresholds1_42.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_42.take 3) (by decide +kernel)

private theorem valid1_42_3 : (thresholds1_42.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_42.drop 3) (by decide +kernel)

theorem valid1_42 : thresholds1_42.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_42 3 valid1_42_0 (valid1_42_3)

private theorem valid1_48_0 : (thresholds1_48.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_48.take 4) (by decide +kernel)

private theorem valid1_48_4 : (thresholds1_48.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_48.drop 4) (by decide +kernel)

theorem valid1_48 : thresholds1_48.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_48 4 valid1_48_0 (valid1_48_4)

private theorem valid1_54_0 : (thresholds1_54.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_54.take 3) (by decide +kernel)

private theorem valid1_54_3 : (thresholds1_54.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_54.drop 3) (by decide +kernel)

theorem valid1_54 : thresholds1_54.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_54 3 valid1_54_0 (valid1_54_3)

private theorem valid1_60_0 : (thresholds1_60.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_60.take 4) (by decide +kernel)

private theorem valid1_60_4 : (thresholds1_60.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_60.drop 4) (by decide +kernel)

theorem valid1_60 : thresholds1_60.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_60 4 valid1_60_0 (valid1_60_4)

private theorem valid1_66_0 : (thresholds1_66.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_66.take 4) (by decide +kernel)

private theorem valid1_66_4 : (thresholds1_66.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_66.drop 4) (by decide +kernel)

theorem valid1_66 : thresholds1_66.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_66 4 valid1_66_0 (valid1_66_4)

private theorem valid1_72_0 : (thresholds1_72.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_72.take 4) (by decide +kernel)

private theorem valid1_72_4 : (thresholds1_72.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_72.drop 4) (by decide +kernel)

theorem valid1_72 : thresholds1_72.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_72 4 valid1_72_0 (valid1_72_4)

private theorem valid1_78_0 : (thresholds1_78.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_78.take 3) (by decide +kernel)

private theorem valid1_78_3 : (thresholds1_78.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_78.drop 3) (by decide +kernel)

theorem valid1_78 : thresholds1_78.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_78 3 valid1_78_0 (valid1_78_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part002

section Pack_Z6970H2307PackedBand01Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_84_0 : (thresholds1_84.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_84.take 4) (by decide +kernel)

private theorem valid1_84_4 : ((thresholds1_84.drop 4).take 1).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 ((thresholds1_84.drop 4).take 1) (by decide +kernel)

private theorem valid1_84_5 : (thresholds1_84.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_84.drop 5) (by decide +kernel)

theorem valid1_84 : thresholds1_84.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_84 4 valid1_84_0 (all_take_drop (checked ⟨1,3,1⟩) (thresholds1_84.drop 4) 1 valid1_84_4 (valid1_84_5))

private theorem valid1_90_0 : (thresholds1_90.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_90.take 4) (by decide +kernel)

private theorem valid1_90_4 : (thresholds1_90.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_90.drop 4) (by decide +kernel)

theorem valid1_90 : thresholds1_90.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_90 4 valid1_90_0 (valid1_90_4)

private theorem valid1_96_0 : (thresholds1_96.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_96.take 3) (by decide +kernel)

private theorem valid1_96_3 : (thresholds1_96.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_96.drop 3) (by decide +kernel)

theorem valid1_96 : thresholds1_96.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_96 3 valid1_96_0 (valid1_96_3)

private theorem valid1_102_0 : (thresholds1_102.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_102.take 5) (by decide +kernel)

private theorem valid1_102_5 : (thresholds1_102.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_102.drop 5) (by decide +kernel)

theorem valid1_102 : thresholds1_102.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_102 5 valid1_102_0 (valid1_102_5)

private theorem valid1_108_0 : (thresholds1_108.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_108.take 4) (by decide +kernel)

private theorem valid1_108_4 : (thresholds1_108.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_108.drop 4) (by decide +kernel)

theorem valid1_108 : thresholds1_108.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_108 4 valid1_108_0 (valid1_108_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part003

section Pack_Z6970H2307PackedBand01Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_114_0 : (thresholds1_114.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_114.take 4) (by decide +kernel)

private theorem valid1_114_4 : (thresholds1_114.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_114.drop 4) (by decide +kernel)

theorem valid1_114 : thresholds1_114.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_114 4 valid1_114_0 (valid1_114_4)

private theorem valid1_120_0 : (thresholds1_120.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_120.take 5) (by decide +kernel)

private theorem valid1_120_5 : (thresholds1_120.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_120.drop 5) (by decide +kernel)

theorem valid1_120 : thresholds1_120.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_120 5 valid1_120_0 (valid1_120_5)

private theorem valid1_126_0 : (thresholds1_126.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_126.take 3) (by decide +kernel)

private theorem valid1_126_3 : (thresholds1_126.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_126.drop 3) (by decide +kernel)

theorem valid1_126 : thresholds1_126.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_126 3 valid1_126_0 (valid1_126_3)

private theorem valid1_132_0 : (thresholds1_132.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_132.take 3) (by decide +kernel)

private theorem valid1_132_3 : (thresholds1_132.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_132.drop 3) (by decide +kernel)

theorem valid1_132 : thresholds1_132.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_132 3 valid1_132_0 (valid1_132_3)

private theorem valid1_138_0 : (thresholds1_138.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_138.take 3) (by decide +kernel)

private theorem valid1_138_3 : (thresholds1_138.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_138.drop 3) (by decide +kernel)

theorem valid1_138 : thresholds1_138.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_138 3 valid1_138_0 (valid1_138_3)

private theorem valid1_144_0 : (thresholds1_144.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_144.take 4) (by decide +kernel)

private theorem valid1_144_4 : (thresholds1_144.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_144.drop 4) (by decide +kernel)

theorem valid1_144 : thresholds1_144.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_144 4 valid1_144_0 (valid1_144_4)

private theorem valid1_150_0 : (thresholds1_150.take 2).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_150.take 2) (by decide +kernel)

private theorem valid1_150_2 : ((thresholds1_150.drop 2).take 1).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 ((thresholds1_150.drop 2).take 1) (by decide +kernel)

private theorem valid1_150_3 : (thresholds1_150.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_150.drop 3) (by decide +kernel)

theorem valid1_150 : thresholds1_150.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_150 2 valid1_150_0 (all_take_drop (checked ⟨1,3,1⟩) (thresholds1_150.drop 2) 1 valid1_150_2 (valid1_150_3))

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part004

section Pack_Z6970H2307PackedBand01Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_156_0 : (thresholds1_156.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_156.take 4) (by decide +kernel)

private theorem valid1_156_4 : (thresholds1_156.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_156.drop 4) (by decide +kernel)

theorem valid1_156 : thresholds1_156.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_156 4 valid1_156_0 (valid1_156_4)

private theorem valid1_162_0 : (thresholds1_162.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_162.take 3) (by decide +kernel)

private theorem valid1_162_3 : (thresholds1_162.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_162.drop 3) (by decide +kernel)

theorem valid1_162 : thresholds1_162.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_162 3 valid1_162_0 (valid1_162_3)

private theorem valid1_168_0 : (thresholds1_168.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_168.take 4) (by decide +kernel)

private theorem valid1_168_4 : (thresholds1_168.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_168.drop 4) (by decide +kernel)

theorem valid1_168 : thresholds1_168.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_168 4 valid1_168_0 (valid1_168_4)

private theorem valid1_174_0 : (thresholds1_174.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_174.take 4) (by decide +kernel)

private theorem valid1_174_4 : (thresholds1_174.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_174.drop 4) (by decide +kernel)

theorem valid1_174 : thresholds1_174.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_174 4 valid1_174_0 (valid1_174_4)

private theorem valid1_180_0 : (thresholds1_180.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_180.take 5) (by decide +kernel)

private theorem valid1_180_5 : (thresholds1_180.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_180.drop 5) (by decide +kernel)

theorem valid1_180 : thresholds1_180.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_180 5 valid1_180_0 (valid1_180_5)

private theorem valid1_186_0 : (thresholds1_186.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_186.take 3) (by decide +kernel)

private theorem valid1_186_3 : (thresholds1_186.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_186.drop 3) (by decide +kernel)

theorem valid1_186 : thresholds1_186.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_186 3 valid1_186_0 (valid1_186_3)

private theorem valid1_192_0 : (thresholds1_192.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_192.take 4) (by decide +kernel)

private theorem valid1_192_4 : (thresholds1_192.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_192.drop 4) (by decide +kernel)

theorem valid1_192 : thresholds1_192.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_192 4 valid1_192_0 (valid1_192_4)

private theorem valid1_198_0 : (thresholds1_198.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_198.take 4) (by decide +kernel)

private theorem valid1_198_4 : (thresholds1_198.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_198.drop 4) (by decide +kernel)

theorem valid1_198 : thresholds1_198.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_198 4 valid1_198_0 (valid1_198_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part005

section Pack_Z6970H2307PackedBand01Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_204_0 : (thresholds1_204.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_204.take 3) (by decide +kernel)

private theorem valid1_204_3 : (thresholds1_204.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_204.drop 3) (by decide +kernel)

theorem valid1_204 : thresholds1_204.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_204 3 valid1_204_0 (valid1_204_3)

private theorem valid1_210_0 : (thresholds1_210.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_210.take 3) (by decide +kernel)

private theorem valid1_210_3 : (thresholds1_210.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_210.drop 3) (by decide +kernel)

theorem valid1_210 : thresholds1_210.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_210 3 valid1_210_0 (valid1_210_3)

private theorem valid1_216_0 : (thresholds1_216.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_216.take 5) (by decide +kernel)

private theorem valid1_216_5 : (thresholds1_216.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_216.drop 5) (by decide +kernel)

theorem valid1_216 : thresholds1_216.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_216 5 valid1_216_0 (valid1_216_5)

private theorem valid1_222_0 : (thresholds1_222.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_222.take 5) (by decide +kernel)

private theorem valid1_222_5 : (thresholds1_222.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_222.drop 5) (by decide +kernel)

theorem valid1_222 : thresholds1_222.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_222 5 valid1_222_0 (valid1_222_5)

private theorem valid1_228_0 : (thresholds1_228.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_228.take 4) (by decide +kernel)

private theorem valid1_228_4 : (thresholds1_228.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_228.drop 4) (by decide +kernel)

theorem valid1_228 : thresholds1_228.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_228 4 valid1_228_0 (valid1_228_4)

private theorem valid1_234_0 : (thresholds1_234.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_234.take 4) (by decide +kernel)

private theorem valid1_234_4 : (thresholds1_234.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_234.drop 4) (by decide +kernel)

theorem valid1_234 : thresholds1_234.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_234 4 valid1_234_0 (valid1_234_4)

private theorem valid1_240_0 : (thresholds1_240.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_240.take 4) (by decide +kernel)

private theorem valid1_240_4 : (thresholds1_240.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_240.drop 4) (by decide +kernel)

theorem valid1_240 : thresholds1_240.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_240 4 valid1_240_0 (valid1_240_4)

private theorem valid1_246_0 : (thresholds1_246.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_246.take 4) (by decide +kernel)

private theorem valid1_246_4 : (thresholds1_246.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_246.drop 4) (by decide +kernel)

theorem valid1_246 : thresholds1_246.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_246 4 valid1_246_0 (valid1_246_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part006

section Pack_Z6970H2307PackedBand01Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_252_0 : (thresholds1_252.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_252.take 4) (by decide +kernel)

private theorem valid1_252_4 : (thresholds1_252.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_252.drop 4) (by decide +kernel)

theorem valid1_252 : thresholds1_252.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_252 4 valid1_252_0 (valid1_252_4)

private theorem valid1_258_0 : (thresholds1_258.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_258.take 4) (by decide +kernel)

private theorem valid1_258_4 : (thresholds1_258.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_258.drop 4) (by decide +kernel)

theorem valid1_258 : thresholds1_258.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_258 4 valid1_258_0 (valid1_258_4)

private theorem valid1_264_0 : (thresholds1_264.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_264.take 5) (by decide +kernel)

private theorem valid1_264_5 : (thresholds1_264.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_264.drop 5) (by decide +kernel)

theorem valid1_264 : thresholds1_264.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_264 5 valid1_264_0 (valid1_264_5)

private theorem valid1_270_0 : (thresholds1_270.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_270.take 5) (by decide +kernel)

private theorem valid1_270_5 : (thresholds1_270.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_270.drop 5) (by decide +kernel)

theorem valid1_270 : thresholds1_270.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_270 5 valid1_270_0 (valid1_270_5)

private theorem valid1_276_0 : (thresholds1_276.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_276.take 4) (by decide +kernel)

private theorem valid1_276_4 : (thresholds1_276.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_276.drop 4) (by decide +kernel)

theorem valid1_276 : thresholds1_276.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_276 4 valid1_276_0 (valid1_276_4)

private theorem valid1_282_0 : (thresholds1_282.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_282.take 4) (by decide +kernel)

private theorem valid1_282_4 : (thresholds1_282.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_282.drop 4) (by decide +kernel)

theorem valid1_282 : thresholds1_282.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_282 4 valid1_282_0 (valid1_282_4)

private theorem valid1_288_0 : (thresholds1_288.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_288.take 4) (by decide +kernel)

private theorem valid1_288_4 : (thresholds1_288.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_288.drop 4) (by decide +kernel)

theorem valid1_288 : thresholds1_288.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_288 4 valid1_288_0 (valid1_288_4)

private theorem valid1_294_0 : (thresholds1_294.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_294.take 3) (by decide +kernel)

private theorem valid1_294_3 : (thresholds1_294.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_294.drop 3) (by decide +kernel)

theorem valid1_294 : thresholds1_294.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_294 3 valid1_294_0 (valid1_294_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part007

section Pack_Z6970H2307PackedBand01Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_300_0 : (thresholds1_300.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_300.take 5) (by decide +kernel)

private theorem valid1_300_5 : (thresholds1_300.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_300.drop 5) (by decide +kernel)

theorem valid1_300 : thresholds1_300.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_300 5 valid1_300_0 (valid1_300_5)

private theorem valid1_306_0 : (thresholds1_306.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_306.take 3) (by decide +kernel)

private theorem valid1_306_3 : (thresholds1_306.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_306.drop 3) (by decide +kernel)

theorem valid1_306 : thresholds1_306.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_306 3 valid1_306_0 (valid1_306_3)

private theorem valid1_312_0 : (thresholds1_312.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_312.take 4) (by decide +kernel)

private theorem valid1_312_4 : (thresholds1_312.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_312.drop 4) (by decide +kernel)

theorem valid1_312 : thresholds1_312.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_312 4 valid1_312_0 (valid1_312_4)

theorem valid1_318 : thresholds1_318.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_318 (by decide +kernel)

private theorem valid1_324_0 : (thresholds1_324.take 1).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_324.take 1) (by decide +kernel)

private theorem valid1_324_1 : (thresholds1_324.drop 1).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_324.drop 1) (by decide +kernel)

theorem valid1_324 : thresholds1_324.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_324 1 valid1_324_0 (valid1_324_1)

private theorem valid1_330_0 : (thresholds1_330.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_330.take 5) (by decide +kernel)

private theorem valid1_330_5 : (thresholds1_330.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_330.drop 5) (by decide +kernel)

theorem valid1_330 : thresholds1_330.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_330 5 valid1_330_0 (valid1_330_5)

theorem valid1_336 : thresholds1_336.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_336 (by decide +kernel)

private theorem valid1_342_0 : (thresholds1_342.take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_342.take 3) (by decide +kernel)

private theorem valid1_342_3 : (thresholds1_342.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_342.drop 3) (by decide +kernel)

theorem valid1_342 : thresholds1_342.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_342 3 valid1_342_0 (valid1_342_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part008

section Pack_Z6970H2307PackedBand01Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_348_0 : (thresholds1_348.take 2).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_348.take 2) (by decide +kernel)

private theorem valid1_348_2 : (thresholds1_348.drop 2).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_348.drop 2) (by decide +kernel)

theorem valid1_348 : thresholds1_348.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_348 2 valid1_348_0 (valid1_348_2)

private theorem valid1_354_0 : (thresholds1_354.take 2).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_354.take 2) (by decide +kernel)

private theorem valid1_354_2 : ((thresholds1_354.drop 2).take 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 ((thresholds1_354.drop 2).take 3) (by decide +kernel)

private theorem valid1_354_5 : (thresholds1_354.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_354.drop 5) (by decide +kernel)

theorem valid1_354 : thresholds1_354.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_354 2 valid1_354_0 (all_take_drop (checked ⟨1,3,1⟩) (thresholds1_354.drop 2) 3 valid1_354_2 (valid1_354_5))

private theorem valid1_360_0 : (thresholds1_360.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_360.take 5) (by decide +kernel)

private theorem valid1_360_5 : (thresholds1_360.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_360.drop 5) (by decide +kernel)

theorem valid1_360 : thresholds1_360.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_360 5 valid1_360_0 (valid1_360_5)

private theorem valid1_366_0 : (thresholds1_366.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_366.take 5) (by decide +kernel)

private theorem valid1_366_5 : (thresholds1_366.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_366.drop 5) (by decide +kernel)

theorem valid1_366 : thresholds1_366.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_366 5 valid1_366_0 (valid1_366_5)

theorem valid1_372 : thresholds1_372.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_372 (by decide +kernel)

private theorem valid1_378_0 : (thresholds1_378.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_378.take 4) (by decide +kernel)

private theorem valid1_378_4 : (thresholds1_378.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_378.drop 4) (by decide +kernel)

theorem valid1_378 : thresholds1_378.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_378 4 valid1_378_0 (valid1_378_4)

theorem valid1_384 : thresholds1_384.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_384 (by decide +kernel)

private theorem valid1_390_0 : (thresholds1_390.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_390.take 5) (by decide +kernel)

private theorem valid1_390_5 : (thresholds1_390.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_390.drop 5) (by decide +kernel)

theorem valid1_390 : thresholds1_390.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_390 5 valid1_390_0 (valid1_390_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part009

section Pack_Z6970H2307PackedBand01Part010

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid1_396_0 : (thresholds1_396.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_396.take 5) (by decide +kernel)

private theorem valid1_396_5 : (thresholds1_396.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_396.drop 5) (by decide +kernel)

theorem valid1_396 : thresholds1_396.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_396 5 valid1_396_0 (valid1_396_5)

theorem valid1_402 : thresholds1_402.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_402 (by decide +kernel)

private theorem valid1_408_0 : (thresholds1_408.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_408.take 5) (by decide +kernel)

private theorem valid1_408_5 : (thresholds1_408.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_408.drop 5) (by decide +kernel)

theorem valid1_408 : thresholds1_408.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_408 5 valid1_408_0 (valid1_408_5)

theorem valid1_414 : thresholds1_414.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_414 (by decide +kernel)

theorem valid1_420 : thresholds1_420.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_420 (by decide +kernel)

theorem valid1_426 : thresholds1_426.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_426 (by decide +kernel)

private theorem valid1_432_0 : (thresholds1_432.take 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_432.take 4) (by decide +kernel)

private theorem valid1_432_4 : (thresholds1_432.drop 4).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_432.drop 4) (by decide +kernel)

theorem valid1_432 : thresholds1_432.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_432 4 valid1_432_0 (valid1_432_4)

private theorem valid1_438_0 : (thresholds1_438.take 2).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_438.take 2) (by decide +kernel)

private theorem valid1_438_2 : ((thresholds1_438.drop 2).take 1).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 ((thresholds1_438.drop 2).take 1) (by decide +kernel)

private theorem valid1_438_3 : (thresholds1_438.drop 3).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_438.drop 3) (by decide +kernel)

theorem valid1_438 : thresholds1_438.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_438 2 valid1_438_0 (all_take_drop (checked ⟨1,3,1⟩) (thresholds1_438.drop 2) 1 valid1_438_2 (valid1_438_3))

theorem valid1_444 : thresholds1_444.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_444 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part010

section Pack_Z6970H2307PackedBand01Part011

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid1_450 : thresholds1_450.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_450 (by decide +kernel)

theorem valid1_456 : thresholds1_456.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_456 (by decide +kernel)

theorem valid1_462 : thresholds1_462.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_462 (by decide +kernel)

theorem valid1_468 : thresholds1_468.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_468 (by decide +kernel)

theorem valid1_474 : thresholds1_474.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_474 (by decide +kernel)

theorem valid1_480 : thresholds1_480.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_480 (by decide +kernel)

theorem valid1_486 : thresholds1_486.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_486 (by decide +kernel)

private theorem valid1_492_0 : (thresholds1_492.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_492.take 5) (by decide +kernel)

private theorem valid1_492_5 : (thresholds1_492.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_492.drop 5) (by decide +kernel)

theorem valid1_492 : thresholds1_492.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_492 5 valid1_492_0 (valid1_492_5)

theorem valid1_498 : thresholds1_498.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_498 (by decide +kernel)

theorem valid1_504 : thresholds1_504.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_504 (by decide +kernel)

theorem valid1_510 : thresholds1_510.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_510 (by decide +kernel)

theorem valid1_516 : thresholds1_516.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_516 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part011

section Pack_Z6970H2307PackedBand01Part012

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid1_522 : thresholds1_522.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_522 (by decide +kernel)

private theorem valid1_528_0 : (thresholds1_528.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_528.take 5) (by decide +kernel)

private theorem valid1_528_5 : (thresholds1_528.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_528.drop 5) (by decide +kernel)

theorem valid1_528 : thresholds1_528.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_528 5 valid1_528_0 (valid1_528_5)

private theorem valid1_534_0 : (thresholds1_534.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_534.take 5) (by decide +kernel)

private theorem valid1_534_5 : (thresholds1_534.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_534.drop 5) (by decide +kernel)

theorem valid1_534 : thresholds1_534.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_534 5 valid1_534_0 (valid1_534_5)

private theorem valid1_540_0 : (thresholds1_540.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_540.take 5) (by decide +kernel)

private theorem valid1_540_5 : (thresholds1_540.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_540.drop 5) (by decide +kernel)

theorem valid1_540 : thresholds1_540.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_540 5 valid1_540_0 (valid1_540_5)

theorem valid1_546 : thresholds1_546.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_546 (by decide +kernel)

theorem valid1_552 : thresholds1_552.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_552 (by decide +kernel)

private theorem valid1_558_0 : (thresholds1_558.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_558.take 5) (by decide +kernel)

private theorem valid1_558_5 : (thresholds1_558.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_558.drop 5) (by decide +kernel)

theorem valid1_558 : thresholds1_558.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_558 5 valid1_558_0 (valid1_558_5)

theorem valid1_564 : thresholds1_564.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_564 (by decide +kernel)

theorem valid1_570 : thresholds1_570.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_570 (by decide +kernel)

private theorem valid1_576_0 : (thresholds1_576.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_576.take 5) (by decide +kernel)

private theorem valid1_576_5 : (thresholds1_576.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_576.drop 5) (by decide +kernel)

theorem valid1_576 : thresholds1_576.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_576 5 valid1_576_0 (valid1_576_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part012

section Pack_Z6970H2307PackedBand01Part013

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid1_582 : thresholds1_582.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_582 (by decide +kernel)

private theorem valid1_588_0 : (thresholds1_588.take 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_588.take 5) (by decide +kernel)

private theorem valid1_588_5 : (thresholds1_588.drop 5).all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 (thresholds1_588.drop 5) (by decide +kernel)

theorem valid1_588 : thresholds1_588.all (checked ⟨1,3,1⟩)=true :=
  all_take_drop (checked ⟨1,3,1⟩) thresholds1_588 5 valid1_588_0 (valid1_588_5)

theorem valid1_594 : thresholds1_594.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_594 (by decide +kernel)

theorem valid1_600 : thresholds1_600.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_600 (by decide +kernel)

theorem valid1_606 : thresholds1_606.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_606 (by decide +kernel)

theorem valid1_612 : thresholds1_612.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_612 (by decide +kernel)

theorem valid1_618 : thresholds1_618.all (checked ⟨1,3,1⟩)=true :=
  checkedVerified ⟨1,3,1⟩ prefixMap1 thresholds1_618 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand01Part013

section Pack_Z6970H2307PackedBand02Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_0_0 : (thresholds2_0.take 2).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_0.take 2) (by decide +kernel)

private theorem valid2_0_2 : ((thresholds2_0.drop 2).take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_0.drop 2).take 3) (by decide +kernel)

private theorem valid2_0_5 : (thresholds2_0.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_0.drop 5) (by decide +kernel)

theorem valid2_0 : thresholds2_0.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_0 2 valid2_0_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_0.drop 2) 3 valid2_0_2 (valid2_0_5))

private theorem valid2_6_0 : (thresholds2_6.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_6.take 4) (by decide +kernel)

private theorem valid2_6_4 : (thresholds2_6.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_6.drop 4) (by decide +kernel)

theorem valid2_6 : thresholds2_6.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_6 4 valid2_6_0 (valid2_6_4)

theorem valid2_12 : thresholds2_12.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_12 (by decide +kernel)

theorem valid2_18 : thresholds2_18.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_18 (by decide +kernel)

theorem valid2_24 : thresholds2_24.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_24 (by decide +kernel)

private theorem valid2_30_0 : (thresholds2_30.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_30.take 3) (by decide +kernel)

private theorem valid2_30_3 : (thresholds2_30.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_30.drop 3) (by decide +kernel)

theorem valid2_30 : thresholds2_30.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_30 3 valid2_30_0 (valid2_30_3)

private theorem valid2_36_0 : (thresholds2_36.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_36.take 4) (by decide +kernel)

private theorem valid2_36_4 : (thresholds2_36.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_36.drop 4) (by decide +kernel)

theorem valid2_36 : thresholds2_36.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_36 4 valid2_36_0 (valid2_36_4)

private theorem valid2_42_0 : (thresholds2_42.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_42.take 4) (by decide +kernel)

private theorem valid2_42_4 : (thresholds2_42.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_42.drop 4) (by decide +kernel)

theorem valid2_42 : thresholds2_42.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_42 4 valid2_42_0 (valid2_42_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part000

section Pack_Z6970H2307PackedBand02Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_48_0 : (thresholds2_48.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_48.take 4) (by decide +kernel)

private theorem valid2_48_4 : (thresholds2_48.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_48.drop 4) (by decide +kernel)

theorem valid2_48 : thresholds2_48.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_48 4 valid2_48_0 (valid2_48_4)

private theorem valid2_54_0 : (thresholds2_54.take 1).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_54.take 1) (by decide +kernel)

private theorem valid2_54_1 : ((thresholds2_54.drop 1).take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_54.drop 1).take 3) (by decide +kernel)

private theorem valid2_54_4 : (thresholds2_54.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_54.drop 4) (by decide +kernel)

theorem valid2_54 : thresholds2_54.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_54 1 valid2_54_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_54.drop 1) 3 valid2_54_1 (valid2_54_4))

private theorem valid2_60_0 : (thresholds2_60.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_60.take 5) (by decide +kernel)

private theorem valid2_60_5 : (thresholds2_60.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_60.drop 5) (by decide +kernel)

theorem valid2_60 : thresholds2_60.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_60 5 valid2_60_0 (valid2_60_5)

private theorem valid2_66_0 : (thresholds2_66.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_66.take 3) (by decide +kernel)

private theorem valid2_66_3 : ((thresholds2_66.drop 3).take 1).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_66.drop 3).take 1) (by decide +kernel)

private theorem valid2_66_4 : (thresholds2_66.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_66.drop 4) (by decide +kernel)

theorem valid2_66 : thresholds2_66.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_66 3 valid2_66_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_66.drop 3) 1 valid2_66_3 (valid2_66_4))

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part001

section Pack_Z6970H2307PackedBand02Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_72_0 : (thresholds2_72.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_72.take 4) (by decide +kernel)

private theorem valid2_72_4 : ((thresholds2_72.drop 4).take 1).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_72.drop 4).take 1) (by decide +kernel)

private theorem valid2_72_5 : (thresholds2_72.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_72.drop 5) (by decide +kernel)

theorem valid2_72 : thresholds2_72.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_72 4 valid2_72_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_72.drop 4) 1 valid2_72_4 (valid2_72_5))

private theorem valid2_78_0 : (thresholds2_78.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_78.take 4) (by decide +kernel)

private theorem valid2_78_4 : (thresholds2_78.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_78.drop 4) (by decide +kernel)

theorem valid2_78 : thresholds2_78.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_78 4 valid2_78_0 (valid2_78_4)

private theorem valid2_84_0 : (thresholds2_84.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_84.take 4) (by decide +kernel)

private theorem valid2_84_4 : (thresholds2_84.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_84.drop 4) (by decide +kernel)

theorem valid2_84 : thresholds2_84.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_84 4 valid2_84_0 (valid2_84_4)

private theorem valid2_90_0 : (thresholds2_90.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_90.take 4) (by decide +kernel)

private theorem valid2_90_4 : (thresholds2_90.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_90.drop 4) (by decide +kernel)

theorem valid2_90 : thresholds2_90.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_90 4 valid2_90_0 (valid2_90_4)

private theorem valid2_96_0 : (thresholds2_96.take 1).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_96.take 1) (by decide +kernel)

private theorem valid2_96_1 : ((thresholds2_96.drop 1).take 1).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_96.drop 1).take 1) (by decide +kernel)

private theorem valid2_96_2 : (thresholds2_96.drop 2).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_96.drop 2) (by decide +kernel)

theorem valid2_96 : thresholds2_96.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_96 1 valid2_96_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_96.drop 1) 1 valid2_96_1 (valid2_96_2))

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part002

section Pack_Z6970H2307PackedBand02Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_102_0 : (thresholds2_102.take 2).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_102.take 2) (by decide +kernel)

private theorem valid2_102_2 : ((thresholds2_102.drop 2).take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_102.drop 2).take 3) (by decide +kernel)

private theorem valid2_102_5 : (thresholds2_102.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_102.drop 5) (by decide +kernel)

theorem valid2_102 : thresholds2_102.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_102 2 valid2_102_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_102.drop 2) 3 valid2_102_2 (valid2_102_5))

private theorem valid2_108_0 : (thresholds2_108.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_108.take 3) (by decide +kernel)

private theorem valid2_108_3 : (thresholds2_108.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_108.drop 3) (by decide +kernel)

theorem valid2_108 : thresholds2_108.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_108 3 valid2_108_0 (valid2_108_3)

private theorem valid2_114_0 : (thresholds2_114.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_114.take 3) (by decide +kernel)

private theorem valid2_114_3 : (thresholds2_114.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_114.drop 3) (by decide +kernel)

theorem valid2_114 : thresholds2_114.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_114 3 valid2_114_0 (valid2_114_3)

private theorem valid2_120_0 : (thresholds2_120.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_120.take 4) (by decide +kernel)

private theorem valid2_120_4 : (thresholds2_120.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_120.drop 4) (by decide +kernel)

theorem valid2_120 : thresholds2_120.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_120 4 valid2_120_0 (valid2_120_4)

private theorem valid2_126_0 : (thresholds2_126.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_126.take 3) (by decide +kernel)

private theorem valid2_126_3 : (thresholds2_126.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_126.drop 3) (by decide +kernel)

theorem valid2_126 : thresholds2_126.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_126 3 valid2_126_0 (valid2_126_3)

private theorem valid2_132_0 : (thresholds2_132.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_132.take 5) (by decide +kernel)

private theorem valid2_132_5 : (thresholds2_132.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_132.drop 5) (by decide +kernel)

theorem valid2_132 : thresholds2_132.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_132 5 valid2_132_0 (valid2_132_5)

private theorem valid2_138_0 : (thresholds2_138.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_138.take 3) (by decide +kernel)

private theorem valid2_138_3 : (thresholds2_138.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_138.drop 3) (by decide +kernel)

theorem valid2_138 : thresholds2_138.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_138 3 valid2_138_0 (valid2_138_3)

private theorem valid2_144_0 : (thresholds2_144.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_144.take 3) (by decide +kernel)

private theorem valid2_144_3 : (thresholds2_144.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_144.drop 3) (by decide +kernel)

theorem valid2_144 : thresholds2_144.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_144 3 valid2_144_0 (valid2_144_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part003

section Pack_Z6970H2307PackedBand02Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_150_0 : (thresholds2_150.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_150.take 3) (by decide +kernel)

private theorem valid2_150_3 : (thresholds2_150.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_150.drop 3) (by decide +kernel)

theorem valid2_150 : thresholds2_150.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_150 3 valid2_150_0 (valid2_150_3)

private theorem valid2_156_0 : (thresholds2_156.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_156.take 4) (by decide +kernel)

private theorem valid2_156_4 : (thresholds2_156.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_156.drop 4) (by decide +kernel)

theorem valid2_156 : thresholds2_156.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_156 4 valid2_156_0 (valid2_156_4)

private theorem valid2_162_0 : (thresholds2_162.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_162.take 5) (by decide +kernel)

private theorem valid2_162_5 : (thresholds2_162.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_162.drop 5) (by decide +kernel)

theorem valid2_162 : thresholds2_162.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_162 5 valid2_162_0 (valid2_162_5)

private theorem valid2_168_0 : (thresholds2_168.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_168.take 3) (by decide +kernel)

private theorem valid2_168_3 : (thresholds2_168.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_168.drop 3) (by decide +kernel)

theorem valid2_168 : thresholds2_168.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_168 3 valid2_168_0 (valid2_168_3)

private theorem valid2_174_0 : (thresholds2_174.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_174.take 4) (by decide +kernel)

private theorem valid2_174_4 : (thresholds2_174.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_174.drop 4) (by decide +kernel)

theorem valid2_174 : thresholds2_174.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_174 4 valid2_174_0 (valid2_174_4)

private theorem valid2_180_0 : (thresholds2_180.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_180.take 4) (by decide +kernel)

private theorem valid2_180_4 : (thresholds2_180.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_180.drop 4) (by decide +kernel)

theorem valid2_180 : thresholds2_180.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_180 4 valid2_180_0 (valid2_180_4)

private theorem valid2_186_0 : (thresholds2_186.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_186.take 5) (by decide +kernel)

private theorem valid2_186_5 : (thresholds2_186.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_186.drop 5) (by decide +kernel)

theorem valid2_186 : thresholds2_186.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_186 5 valid2_186_0 (valid2_186_5)

private theorem valid2_192_0 : (thresholds2_192.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_192.take 4) (by decide +kernel)

private theorem valid2_192_4 : (thresholds2_192.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_192.drop 4) (by decide +kernel)

theorem valid2_192 : thresholds2_192.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_192 4 valid2_192_0 (valid2_192_4)

private theorem valid2_198_0 : (thresholds2_198.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_198.take 4) (by decide +kernel)

private theorem valid2_198_4 : (thresholds2_198.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_198.drop 4) (by decide +kernel)

theorem valid2_198 : thresholds2_198.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_198 4 valid2_198_0 (valid2_198_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part004

section Pack_Z6970H2307PackedBand02Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_204_0 : (thresholds2_204.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_204.take 4) (by decide +kernel)

private theorem valid2_204_4 : (thresholds2_204.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_204.drop 4) (by decide +kernel)

theorem valid2_204 : thresholds2_204.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_204 4 valid2_204_0 (valid2_204_4)

private theorem valid2_210_0 : (thresholds2_210.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_210.take 4) (by decide +kernel)

private theorem valid2_210_4 : (thresholds2_210.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_210.drop 4) (by decide +kernel)

theorem valid2_210 : thresholds2_210.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_210 4 valid2_210_0 (valid2_210_4)

private theorem valid2_216_0 : (thresholds2_216.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_216.take 4) (by decide +kernel)

private theorem valid2_216_4 : (thresholds2_216.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_216.drop 4) (by decide +kernel)

theorem valid2_216 : thresholds2_216.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_216 4 valid2_216_0 (valid2_216_4)

private theorem valid2_222_0 : (thresholds2_222.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_222.take 4) (by decide +kernel)

private theorem valid2_222_4 : (thresholds2_222.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_222.drop 4) (by decide +kernel)

theorem valid2_222 : thresholds2_222.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_222 4 valid2_222_0 (valid2_222_4)

private theorem valid2_228_0 : (thresholds2_228.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_228.take 4) (by decide +kernel)

private theorem valid2_228_4 : (thresholds2_228.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_228.drop 4) (by decide +kernel)

theorem valid2_228 : thresholds2_228.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_228 4 valid2_228_0 (valid2_228_4)

private theorem valid2_234_0 : (thresholds2_234.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_234.take 5) (by decide +kernel)

private theorem valid2_234_5 : (thresholds2_234.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_234.drop 5) (by decide +kernel)

theorem valid2_234 : thresholds2_234.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_234 5 valid2_234_0 (valid2_234_5)

private theorem valid2_240_0 : (thresholds2_240.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_240.take 4) (by decide +kernel)

private theorem valid2_240_4 : (thresholds2_240.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_240.drop 4) (by decide +kernel)

theorem valid2_240 : thresholds2_240.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_240 4 valid2_240_0 (valid2_240_4)

private theorem valid2_246_0 : (thresholds2_246.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_246.take 4) (by decide +kernel)

private theorem valid2_246_4 : (thresholds2_246.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_246.drop 4) (by decide +kernel)

theorem valid2_246 : thresholds2_246.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_246 4 valid2_246_0 (valid2_246_4)

private theorem valid2_252_0 : (thresholds2_252.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_252.take 5) (by decide +kernel)

private theorem valid2_252_5 : (thresholds2_252.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_252.drop 5) (by decide +kernel)

theorem valid2_252 : thresholds2_252.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_252 5 valid2_252_0 (valid2_252_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part005

section Pack_Z6970H2307PackedBand02Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_258_0 : (thresholds2_258.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_258.take 4) (by decide +kernel)

private theorem valid2_258_4 : (thresholds2_258.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_258.drop 4) (by decide +kernel)

theorem valid2_258 : thresholds2_258.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_258 4 valid2_258_0 (valid2_258_4)

private theorem valid2_264_0 : (thresholds2_264.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_264.take 5) (by decide +kernel)

private theorem valid2_264_5 : (thresholds2_264.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_264.drop 5) (by decide +kernel)

theorem valid2_264 : thresholds2_264.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_264 5 valid2_264_0 (valid2_264_5)

private theorem valid2_270_0 : (thresholds2_270.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_270.take 5) (by decide +kernel)

private theorem valid2_270_5 : (thresholds2_270.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_270.drop 5) (by decide +kernel)

theorem valid2_270 : thresholds2_270.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_270 5 valid2_270_0 (valid2_270_5)

private theorem valid2_276_0 : (thresholds2_276.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_276.take 5) (by decide +kernel)

private theorem valid2_276_5 : (thresholds2_276.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_276.drop 5) (by decide +kernel)

theorem valid2_276 : thresholds2_276.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_276 5 valid2_276_0 (valid2_276_5)

theorem valid2_282 : thresholds2_282.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_282 (by decide +kernel)

private theorem valid2_288_0 : (thresholds2_288.take 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_288.take 3) (by decide +kernel)

private theorem valid2_288_3 : (thresholds2_288.drop 3).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_288.drop 3) (by decide +kernel)

theorem valid2_288 : thresholds2_288.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_288 3 valid2_288_0 (valid2_288_3)

private theorem valid2_294_0 : (thresholds2_294.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_294.take 4) (by decide +kernel)

private theorem valid2_294_4 : (thresholds2_294.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_294.drop 4) (by decide +kernel)

theorem valid2_294 : thresholds2_294.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_294 4 valid2_294_0 (valid2_294_4)

private theorem valid2_300_0 : (thresholds2_300.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_300.take 5) (by decide +kernel)

private theorem valid2_300_5 : (thresholds2_300.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_300.drop 5) (by decide +kernel)

theorem valid2_300 : thresholds2_300.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_300 5 valid2_300_0 (valid2_300_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part006

section Pack_Z6970H2307PackedBand02Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_306_0 : (thresholds2_306.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_306.take 5) (by decide +kernel)

private theorem valid2_306_5 : (thresholds2_306.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_306.drop 5) (by decide +kernel)

theorem valid2_306 : thresholds2_306.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_306 5 valid2_306_0 (valid2_306_5)

private theorem valid2_312_0 : (thresholds2_312.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_312.take 5) (by decide +kernel)

private theorem valid2_312_5 : (thresholds2_312.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_312.drop 5) (by decide +kernel)

theorem valid2_312 : thresholds2_312.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_312 5 valid2_312_0 (valid2_312_5)

theorem valid2_318 : thresholds2_318.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_318 (by decide +kernel)

private theorem valid2_324_0 : (thresholds2_324.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_324.take 5) (by decide +kernel)

private theorem valid2_324_5 : (thresholds2_324.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_324.drop 5) (by decide +kernel)

theorem valid2_324 : thresholds2_324.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_324 5 valid2_324_0 (valid2_324_5)

theorem valid2_330 : thresholds2_330.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_330 (by decide +kernel)

private theorem valid2_336_0 : (thresholds2_336.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_336.take 5) (by decide +kernel)

private theorem valid2_336_5 : (thresholds2_336.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_336.drop 5) (by decide +kernel)

theorem valid2_336 : thresholds2_336.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_336 5 valid2_336_0 (valid2_336_5)

private theorem valid2_342_0 : (thresholds2_342.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_342.take 5) (by decide +kernel)

private theorem valid2_342_5 : (thresholds2_342.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_342.drop 5) (by decide +kernel)

theorem valid2_342 : thresholds2_342.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_342 5 valid2_342_0 (valid2_342_5)

private theorem valid2_348_0 : (thresholds2_348.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_348.take 4) (by decide +kernel)

private theorem valid2_348_4 : ((thresholds2_348.drop 4).take 1).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 ((thresholds2_348.drop 4).take 1) (by decide +kernel)

private theorem valid2_348_5 : (thresholds2_348.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_348.drop 5) (by decide +kernel)

theorem valid2_348 : thresholds2_348.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_348 4 valid2_348_0 (all_take_drop (checked ⟨2,3,1⟩) (thresholds2_348.drop 4) 1 valid2_348_4 (valid2_348_5))

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part007

section Pack_Z6970H2307PackedBand02Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid2_354_0 : (thresholds2_354.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_354.take 4) (by decide +kernel)

private theorem valid2_354_4 : (thresholds2_354.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_354.drop 4) (by decide +kernel)

theorem valid2_354 : thresholds2_354.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_354 4 valid2_354_0 (valid2_354_4)

private theorem valid2_360_0 : (thresholds2_360.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_360.take 4) (by decide +kernel)

private theorem valid2_360_4 : (thresholds2_360.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_360.drop 4) (by decide +kernel)

theorem valid2_360 : thresholds2_360.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_360 4 valid2_360_0 (valid2_360_4)

private theorem valid2_366_0 : (thresholds2_366.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_366.take 5) (by decide +kernel)

private theorem valid2_366_5 : (thresholds2_366.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_366.drop 5) (by decide +kernel)

theorem valid2_366 : thresholds2_366.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_366 5 valid2_366_0 (valid2_366_5)

private theorem valid2_372_0 : (thresholds2_372.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_372.take 5) (by decide +kernel)

private theorem valid2_372_5 : (thresholds2_372.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_372.drop 5) (by decide +kernel)

theorem valid2_372 : thresholds2_372.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_372 5 valid2_372_0 (valid2_372_5)

theorem valid2_378 : thresholds2_378.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_378 (by decide +kernel)

private theorem valid2_384_0 : (thresholds2_384.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_384.take 4) (by decide +kernel)

private theorem valid2_384_4 : (thresholds2_384.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_384.drop 4) (by decide +kernel)

theorem valid2_384 : thresholds2_384.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_384 4 valid2_384_0 (valid2_384_4)

theorem valid2_390 : thresholds2_390.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_390 (by decide +kernel)

theorem valid2_396 : thresholds2_396.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_396 (by decide +kernel)

theorem valid2_402 : thresholds2_402.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_402 (by decide +kernel)

private theorem valid2_408_0 : (thresholds2_408.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_408.take 5) (by decide +kernel)

private theorem valid2_408_5 : (thresholds2_408.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_408.drop 5) (by decide +kernel)

theorem valid2_408 : thresholds2_408.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_408 5 valid2_408_0 (valid2_408_5)

theorem valid2_414 : thresholds2_414.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_414 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part008

section Pack_Z6970H2307PackedBand02Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid2_420 : thresholds2_420.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_420 (by decide +kernel)

theorem valid2_426 : thresholds2_426.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_426 (by decide +kernel)

private theorem valid2_432_0 : (thresholds2_432.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_432.take 5) (by decide +kernel)

private theorem valid2_432_5 : (thresholds2_432.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_432.drop 5) (by decide +kernel)

theorem valid2_432 : thresholds2_432.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_432 5 valid2_432_0 (valid2_432_5)

theorem valid2_438 : thresholds2_438.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_438 (by decide +kernel)

theorem valid2_444 : thresholds2_444.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_444 (by decide +kernel)

theorem valid2_450 : thresholds2_450.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_450 (by decide +kernel)

theorem valid2_456 : thresholds2_456.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_456 (by decide +kernel)

private theorem valid2_462_0 : (thresholds2_462.take 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_462.take 5) (by decide +kernel)

private theorem valid2_462_5 : (thresholds2_462.drop 5).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_462.drop 5) (by decide +kernel)

theorem valid2_462 : thresholds2_462.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_462 5 valid2_462_0 (valid2_462_5)

theorem valid2_468 : thresholds2_468.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_468 (by decide +kernel)

theorem valid2_474 : thresholds2_474.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_474 (by decide +kernel)

theorem valid2_480 : thresholds2_480.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_480 (by decide +kernel)

theorem valid2_486 : thresholds2_486.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_486 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part009

section Pack_Z6970H2307PackedBand02Part010

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid2_492 : thresholds2_492.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_492 (by decide +kernel)

theorem valid2_498 : thresholds2_498.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_498 (by decide +kernel)

theorem valid2_504 : thresholds2_504.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_504 (by decide +kernel)

private theorem valid2_510_0 : (thresholds2_510.take 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_510.take 4) (by decide +kernel)

private theorem valid2_510_4 : (thresholds2_510.drop 4).all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 (thresholds2_510.drop 4) (by decide +kernel)

theorem valid2_510 : thresholds2_510.all (checked ⟨2,3,1⟩)=true :=
  all_take_drop (checked ⟨2,3,1⟩) thresholds2_510 4 valid2_510_0 (valid2_510_4)

theorem valid2_516 : thresholds2_516.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_516 (by decide +kernel)

theorem valid2_522 : thresholds2_522.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_522 (by decide +kernel)

theorem valid2_528 : thresholds2_528.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_528 (by decide +kernel)

theorem valid2_534 : thresholds2_534.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_534 (by decide +kernel)

theorem valid2_540 : thresholds2_540.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_540 (by decide +kernel)

theorem valid2_546 : thresholds2_546.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_546 (by decide +kernel)

theorem valid2_552 : thresholds2_552.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_552 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part010

section Pack_Z6970H2307PackedBand02Part011

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid2_558 : thresholds2_558.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_558 (by decide +kernel)

theorem valid2_564 : thresholds2_564.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_564 (by decide +kernel)

theorem valid2_570 : thresholds2_570.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_570 (by decide +kernel)

theorem valid2_576 : thresholds2_576.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_576 (by decide +kernel)

theorem valid2_582 : thresholds2_582.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_582 (by decide +kernel)

theorem valid2_588 : thresholds2_588.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_588 (by decide +kernel)

theorem valid2_594 : thresholds2_594.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_594 (by decide +kernel)

theorem valid2_600 : thresholds2_600.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_600 (by decide +kernel)

theorem valid2_606 : thresholds2_606.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_606 (by decide +kernel)

theorem valid2_612 : thresholds2_612.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_612 (by decide +kernel)

theorem valid2_618 : thresholds2_618.all (checked ⟨2,3,1⟩)=true :=
  checkedVerified ⟨2,3,1⟩ prefixMap2 thresholds2_618 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand02Part011

section Pack_Z6970H2307PackedBand03Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_0_0 : (thresholds3_0.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_0.take 3) (by decide +kernel)

private theorem valid3_0_3 : (thresholds3_0.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_0.drop 3) (by decide +kernel)

theorem valid3_0 : thresholds3_0.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_0 3 valid3_0_0 (valid3_0_3)

theorem valid3_6 : thresholds3_6.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_6 (by decide +kernel)

theorem valid3_12 : thresholds3_12.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_12 (by decide +kernel)

theorem valid3_18 : thresholds3_18.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_18 (by decide +kernel)

private theorem valid3_24_0 : (thresholds3_24.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_24.take 5) (by decide +kernel)

private theorem valid3_24_5 : (thresholds3_24.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_24.drop 5) (by decide +kernel)

theorem valid3_24 : thresholds3_24.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_24 5 valid3_24_0 (valid3_24_5)

private theorem valid3_30_0 : (thresholds3_30.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_30.take 5) (by decide +kernel)

private theorem valid3_30_5 : (thresholds3_30.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_30.drop 5) (by decide +kernel)

theorem valid3_30 : thresholds3_30.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_30 5 valid3_30_0 (valid3_30_5)

private theorem valid3_36_0 : (thresholds3_36.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_36.take 4) (by decide +kernel)

private theorem valid3_36_4 : (thresholds3_36.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_36.drop 4) (by decide +kernel)

theorem valid3_36 : thresholds3_36.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_36 4 valid3_36_0 (valid3_36_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part000

section Pack_Z6970H2307PackedBand03Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_42_0 : (thresholds3_42.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_42.take 4) (by decide +kernel)

private theorem valid3_42_4 : ((thresholds3_42.drop 4).take 1).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 ((thresholds3_42.drop 4).take 1) (by decide +kernel)

private theorem valid3_42_5 : (thresholds3_42.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_42.drop 5) (by decide +kernel)

theorem valid3_42 : thresholds3_42.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_42 4 valid3_42_0 (all_take_drop (checked ⟨3,3,1⟩) (thresholds3_42.drop 4) 1 valid3_42_4 (valid3_42_5))

private theorem valid3_48_0 : (thresholds3_48.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_48.take 3) (by decide +kernel)

private theorem valid3_48_3 : (thresholds3_48.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_48.drop 3) (by decide +kernel)

theorem valid3_48 : thresholds3_48.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_48 3 valid3_48_0 (valid3_48_3)

private theorem valid3_54_0 : (thresholds3_54.take 2).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_54.take 2) (by decide +kernel)

private theorem valid3_54_2 : (thresholds3_54.drop 2).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_54.drop 2) (by decide +kernel)

theorem valid3_54 : thresholds3_54.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_54 2 valid3_54_0 (valid3_54_2)

private theorem valid3_60_0 : (thresholds3_60.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_60.take 4) (by decide +kernel)

private theorem valid3_60_4 : (thresholds3_60.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_60.drop 4) (by decide +kernel)

theorem valid3_60 : thresholds3_60.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_60 4 valid3_60_0 (valid3_60_4)

private theorem valid3_66_0 : (thresholds3_66.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_66.take 4) (by decide +kernel)

private theorem valid3_66_4 : (thresholds3_66.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_66.drop 4) (by decide +kernel)

theorem valid3_66 : thresholds3_66.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_66 4 valid3_66_0 (valid3_66_4)

private theorem valid3_72_0 : (thresholds3_72.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_72.take 4) (by decide +kernel)

private theorem valid3_72_4 : (thresholds3_72.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_72.drop 4) (by decide +kernel)

theorem valid3_72 : thresholds3_72.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_72 4 valid3_72_0 (valid3_72_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part001

section Pack_Z6970H2307PackedBand03Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_78_0 : (thresholds3_78.take 1).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_78.take 1) (by decide +kernel)

private theorem valid3_78_1 : (thresholds3_78.drop 1).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_78.drop 1) (by decide +kernel)

theorem valid3_78 : thresholds3_78.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_78 1 valid3_78_0 (valid3_78_1)

private theorem valid3_84_0 : (thresholds3_84.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_84.take 5) (by decide +kernel)

private theorem valid3_84_5 : (thresholds3_84.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_84.drop 5) (by decide +kernel)

theorem valid3_84 : thresholds3_84.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_84 5 valid3_84_0 (valid3_84_5)

private theorem valid3_90_0 : (thresholds3_90.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_90.take 3) (by decide +kernel)

private theorem valid3_90_3 : (thresholds3_90.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_90.drop 3) (by decide +kernel)

theorem valid3_90 : thresholds3_90.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_90 3 valid3_90_0 (valid3_90_3)

private theorem valid3_96_0 : (thresholds3_96.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_96.take 4) (by decide +kernel)

private theorem valid3_96_4 : (thresholds3_96.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_96.drop 4) (by decide +kernel)

theorem valid3_96 : thresholds3_96.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_96 4 valid3_96_0 (valid3_96_4)

private theorem valid3_102_0 : (thresholds3_102.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_102.take 4) (by decide +kernel)

private theorem valid3_102_4 : (thresholds3_102.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_102.drop 4) (by decide +kernel)

theorem valid3_102 : thresholds3_102.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_102 4 valid3_102_0 (valid3_102_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part002

section Pack_Z6970H2307PackedBand03Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_108_0 : (thresholds3_108.take 2).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_108.take 2) (by decide +kernel)

private theorem valid3_108_2 : ((thresholds3_108.drop 2).take 1).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 ((thresholds3_108.drop 2).take 1) (by decide +kernel)

private theorem valid3_108_3 : (thresholds3_108.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_108.drop 3) (by decide +kernel)

theorem valid3_108 : thresholds3_108.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_108 2 valid3_108_0 (all_take_drop (checked ⟨3,3,1⟩) (thresholds3_108.drop 2) 1 valid3_108_2 (valid3_108_3))

private theorem valid3_114_0 : (thresholds3_114.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_114.take 4) (by decide +kernel)

private theorem valid3_114_4 : (thresholds3_114.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_114.drop 4) (by decide +kernel)

theorem valid3_114 : thresholds3_114.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_114 4 valid3_114_0 (valid3_114_4)

private theorem valid3_120_0 : (thresholds3_120.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_120.take 3) (by decide +kernel)

private theorem valid3_120_3 : (thresholds3_120.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_120.drop 3) (by decide +kernel)

theorem valid3_120 : thresholds3_120.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_120 3 valid3_120_0 (valid3_120_3)

private theorem valid3_126_0 : (thresholds3_126.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_126.take 4) (by decide +kernel)

private theorem valid3_126_4 : (thresholds3_126.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_126.drop 4) (by decide +kernel)

theorem valid3_126 : thresholds3_126.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_126 4 valid3_126_0 (valid3_126_4)

private theorem valid3_132_0 : (thresholds3_132.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_132.take 3) (by decide +kernel)

private theorem valid3_132_3 : (thresholds3_132.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_132.drop 3) (by decide +kernel)

theorem valid3_132 : thresholds3_132.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_132 3 valid3_132_0 (valid3_132_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part003

section Pack_Z6970H2307PackedBand03Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_138_0 : (thresholds3_138.take 1).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_138.take 1) (by decide +kernel)

private theorem valid3_138_1 : ((thresholds3_138.drop 1).take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 ((thresholds3_138.drop 1).take 3) (by decide +kernel)

private theorem valid3_138_4 : (thresholds3_138.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_138.drop 4) (by decide +kernel)

theorem valid3_138 : thresholds3_138.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_138 1 valid3_138_0 (all_take_drop (checked ⟨3,3,1⟩) (thresholds3_138.drop 1) 3 valid3_138_1 (valid3_138_4))

private theorem valid3_144_0 : (thresholds3_144.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_144.take 5) (by decide +kernel)

private theorem valid3_144_5 : (thresholds3_144.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_144.drop 5) (by decide +kernel)

theorem valid3_144 : thresholds3_144.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_144 5 valid3_144_0 (valid3_144_5)

private theorem valid3_150_0 : (thresholds3_150.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_150.take 3) (by decide +kernel)

private theorem valid3_150_3 : (thresholds3_150.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_150.drop 3) (by decide +kernel)

theorem valid3_150 : thresholds3_150.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_150 3 valid3_150_0 (valid3_150_3)

private theorem valid3_156_0 : (thresholds3_156.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_156.take 3) (by decide +kernel)

private theorem valid3_156_3 : (thresholds3_156.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_156.drop 3) (by decide +kernel)

theorem valid3_156 : thresholds3_156.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_156 3 valid3_156_0 (valid3_156_3)

private theorem valid3_162_0 : (thresholds3_162.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_162.take 4) (by decide +kernel)

private theorem valid3_162_4 : (thresholds3_162.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_162.drop 4) (by decide +kernel)

theorem valid3_162 : thresholds3_162.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_162 4 valid3_162_0 (valid3_162_4)

private theorem valid3_168_0 : (thresholds3_168.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_168.take 4) (by decide +kernel)

private theorem valid3_168_4 : (thresholds3_168.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_168.drop 4) (by decide +kernel)

theorem valid3_168 : thresholds3_168.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_168 4 valid3_168_0 (valid3_168_4)

private theorem valid3_174_0 : (thresholds3_174.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_174.take 4) (by decide +kernel)

private theorem valid3_174_4 : ((thresholds3_174.drop 4).take 1).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 ((thresholds3_174.drop 4).take 1) (by decide +kernel)

private theorem valid3_174_5 : (thresholds3_174.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_174.drop 5) (by decide +kernel)

theorem valid3_174 : thresholds3_174.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_174 4 valid3_174_0 (all_take_drop (checked ⟨3,3,1⟩) (thresholds3_174.drop 4) 1 valid3_174_4 (valid3_174_5))

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part004

section Pack_Z6970H2307PackedBand03Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_180_0 : (thresholds3_180.take 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_180.take 3) (by decide +kernel)

private theorem valid3_180_3 : (thresholds3_180.drop 3).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_180.drop 3) (by decide +kernel)

theorem valid3_180 : thresholds3_180.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_180 3 valid3_180_0 (valid3_180_3)

private theorem valid3_186_0 : (thresholds3_186.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_186.take 4) (by decide +kernel)

private theorem valid3_186_4 : (thresholds3_186.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_186.drop 4) (by decide +kernel)

theorem valid3_186 : thresholds3_186.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_186 4 valid3_186_0 (valid3_186_4)

private theorem valid3_192_0 : (thresholds3_192.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_192.take 4) (by decide +kernel)

private theorem valid3_192_4 : (thresholds3_192.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_192.drop 4) (by decide +kernel)

theorem valid3_192 : thresholds3_192.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_192 4 valid3_192_0 (valid3_192_4)

private theorem valid3_198_0 : (thresholds3_198.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_198.take 4) (by decide +kernel)

private theorem valid3_198_4 : (thresholds3_198.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_198.drop 4) (by decide +kernel)

theorem valid3_198 : thresholds3_198.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_198 4 valid3_198_0 (valid3_198_4)

private theorem valid3_204_0 : (thresholds3_204.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_204.take 5) (by decide +kernel)

private theorem valid3_204_5 : (thresholds3_204.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_204.drop 5) (by decide +kernel)

theorem valid3_204 : thresholds3_204.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_204 5 valid3_204_0 (valid3_204_5)

private theorem valid3_210_0 : (thresholds3_210.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_210.take 5) (by decide +kernel)

private theorem valid3_210_5 : (thresholds3_210.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_210.drop 5) (by decide +kernel)

theorem valid3_210 : thresholds3_210.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_210 5 valid3_210_0 (valid3_210_5)

private theorem valid3_216_0 : (thresholds3_216.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_216.take 4) (by decide +kernel)

private theorem valid3_216_4 : (thresholds3_216.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_216.drop 4) (by decide +kernel)

theorem valid3_216 : thresholds3_216.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_216 4 valid3_216_0 (valid3_216_4)

private theorem valid3_222_0 : (thresholds3_222.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_222.take 4) (by decide +kernel)

private theorem valid3_222_4 : (thresholds3_222.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_222.drop 4) (by decide +kernel)

theorem valid3_222 : thresholds3_222.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_222 4 valid3_222_0 (valid3_222_4)

private theorem valid3_228_0 : (thresholds3_228.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_228.take 5) (by decide +kernel)

private theorem valid3_228_5 : (thresholds3_228.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_228.drop 5) (by decide +kernel)

theorem valid3_228 : thresholds3_228.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_228 5 valid3_228_0 (valid3_228_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part005

section Pack_Z6970H2307PackedBand03Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_234_0 : (thresholds3_234.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_234.take 4) (by decide +kernel)

private theorem valid3_234_4 : (thresholds3_234.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_234.drop 4) (by decide +kernel)

theorem valid3_234 : thresholds3_234.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_234 4 valid3_234_0 (valid3_234_4)

private theorem valid3_240_0 : (thresholds3_240.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_240.take 4) (by decide +kernel)

private theorem valid3_240_4 : (thresholds3_240.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_240.drop 4) (by decide +kernel)

theorem valid3_240 : thresholds3_240.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_240 4 valid3_240_0 (valid3_240_4)

private theorem valid3_246_0 : (thresholds3_246.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_246.take 4) (by decide +kernel)

private theorem valid3_246_4 : (thresholds3_246.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_246.drop 4) (by decide +kernel)

theorem valid3_246 : thresholds3_246.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_246 4 valid3_246_0 (valid3_246_4)

theorem valid3_252 : thresholds3_252.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_252 (by decide +kernel)

private theorem valid3_258_0 : (thresholds3_258.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_258.take 4) (by decide +kernel)

private theorem valid3_258_4 : (thresholds3_258.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_258.drop 4) (by decide +kernel)

theorem valid3_258 : thresholds3_258.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_258 4 valid3_258_0 (valid3_258_4)

private theorem valid3_264_0 : (thresholds3_264.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_264.take 5) (by decide +kernel)

private theorem valid3_264_5 : (thresholds3_264.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_264.drop 5) (by decide +kernel)

theorem valid3_264 : thresholds3_264.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_264 5 valid3_264_0 (valid3_264_5)

private theorem valid3_270_0 : (thresholds3_270.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_270.take 4) (by decide +kernel)

private theorem valid3_270_4 : (thresholds3_270.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_270.drop 4) (by decide +kernel)

theorem valid3_270 : thresholds3_270.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_270 4 valid3_270_0 (valid3_270_4)

private theorem valid3_276_0 : (thresholds3_276.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_276.take 5) (by decide +kernel)

private theorem valid3_276_5 : (thresholds3_276.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_276.drop 5) (by decide +kernel)

theorem valid3_276 : thresholds3_276.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_276 5 valid3_276_0 (valid3_276_5)

private theorem valid3_282_0 : (thresholds3_282.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_282.take 5) (by decide +kernel)

private theorem valid3_282_5 : (thresholds3_282.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_282.drop 5) (by decide +kernel)

theorem valid3_282 : thresholds3_282.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_282 5 valid3_282_0 (valid3_282_5)

private theorem valid3_288_0 : (thresholds3_288.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_288.take 5) (by decide +kernel)

private theorem valid3_288_5 : (thresholds3_288.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_288.drop 5) (by decide +kernel)

theorem valid3_288 : thresholds3_288.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_288 5 valid3_288_0 (valid3_288_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part006

section Pack_Z6970H2307PackedBand03Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid3_294 : thresholds3_294.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_294 (by decide +kernel)

private theorem valid3_300_0 : (thresholds3_300.take 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_300.take 4) (by decide +kernel)

private theorem valid3_300_4 : (thresholds3_300.drop 4).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_300.drop 4) (by decide +kernel)

theorem valid3_300 : thresholds3_300.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_300 4 valid3_300_0 (valid3_300_4)

private theorem valid3_306_0 : (thresholds3_306.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_306.take 5) (by decide +kernel)

private theorem valid3_306_5 : (thresholds3_306.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_306.drop 5) (by decide +kernel)

theorem valid3_306 : thresholds3_306.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_306 5 valid3_306_0 (valid3_306_5)

theorem valid3_312 : thresholds3_312.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_312 (by decide +kernel)

private theorem valid3_318_0 : (thresholds3_318.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_318.take 5) (by decide +kernel)

private theorem valid3_318_5 : (thresholds3_318.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_318.drop 5) (by decide +kernel)

theorem valid3_318 : thresholds3_318.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_318 5 valid3_318_0 (valid3_318_5)

theorem valid3_324 : thresholds3_324.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_324 (by decide +kernel)

private theorem valid3_330_0 : (thresholds3_330.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_330.take 5) (by decide +kernel)

private theorem valid3_330_5 : (thresholds3_330.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_330.drop 5) (by decide +kernel)

theorem valid3_330 : thresholds3_330.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_330 5 valid3_330_0 (valid3_330_5)

theorem valid3_336 : thresholds3_336.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_336 (by decide +kernel)

theorem valid3_342 : thresholds3_342.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_342 (by decide +kernel)

theorem valid3_348 : thresholds3_348.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_348 (by decide +kernel)

private theorem valid3_354_0 : (thresholds3_354.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_354.take 5) (by decide +kernel)

private theorem valid3_354_5 : (thresholds3_354.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_354.drop 5) (by decide +kernel)

theorem valid3_354 : thresholds3_354.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_354 5 valid3_354_0 (valid3_354_5)

theorem valid3_360 : thresholds3_360.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_360 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part007

section Pack_Z6970H2307PackedBand03Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid3_366_0 : (thresholds3_366.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_366.take 5) (by decide +kernel)

private theorem valid3_366_5 : (thresholds3_366.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_366.drop 5) (by decide +kernel)

theorem valid3_366 : thresholds3_366.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_366 5 valid3_366_0 (valid3_366_5)

theorem valid3_372 : thresholds3_372.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_372 (by decide +kernel)

theorem valid3_378 : thresholds3_378.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_378 (by decide +kernel)

theorem valid3_384 : thresholds3_384.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_384 (by decide +kernel)

private theorem valid3_390_0 : (thresholds3_390.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_390.take 5) (by decide +kernel)

private theorem valid3_390_5 : (thresholds3_390.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_390.drop 5) (by decide +kernel)

theorem valid3_390 : thresholds3_390.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_390 5 valid3_390_0 (valid3_390_5)

theorem valid3_396 : thresholds3_396.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_396 (by decide +kernel)

theorem valid3_402 : thresholds3_402.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_402 (by decide +kernel)

theorem valid3_408 : thresholds3_408.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_408 (by decide +kernel)

theorem valid3_414 : thresholds3_414.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_414 (by decide +kernel)

theorem valid3_420 : thresholds3_420.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_420 (by decide +kernel)

theorem valid3_426 : thresholds3_426.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_426 (by decide +kernel)

theorem valid3_432 : thresholds3_432.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_432 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part008

section Pack_Z6970H2307PackedBand03Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid3_438 : thresholds3_438.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_438 (by decide +kernel)

private theorem valid3_444_0 : (thresholds3_444.take 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_444.take 5) (by decide +kernel)

private theorem valid3_444_5 : (thresholds3_444.drop 5).all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 (thresholds3_444.drop 5) (by decide +kernel)

theorem valid3_444 : thresholds3_444.all (checked ⟨3,3,1⟩)=true :=
  all_take_drop (checked ⟨3,3,1⟩) thresholds3_444 5 valid3_444_0 (valid3_444_5)

theorem valid3_450 : thresholds3_450.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_450 (by decide +kernel)

theorem valid3_456 : thresholds3_456.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_456 (by decide +kernel)

theorem valid3_462 : thresholds3_462.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_462 (by decide +kernel)

theorem valid3_468 : thresholds3_468.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_468 (by decide +kernel)

theorem valid3_474 : thresholds3_474.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_474 (by decide +kernel)

theorem valid3_480 : thresholds3_480.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_480 (by decide +kernel)

theorem valid3_486 : thresholds3_486.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_486 (by decide +kernel)

theorem valid3_492 : thresholds3_492.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_492 (by decide +kernel)

theorem valid3_498 : thresholds3_498.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_498 (by decide +kernel)

theorem valid3_504 : thresholds3_504.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_504 (by decide +kernel)

theorem valid3_510 : thresholds3_510.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_510 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part009

section Pack_Z6970H2307PackedBand03Part010

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid3_516 : thresholds3_516.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_516 (by decide +kernel)

theorem valid3_522 : thresholds3_522.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_522 (by decide +kernel)

theorem valid3_528 : thresholds3_528.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_528 (by decide +kernel)

theorem valid3_534 : thresholds3_534.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_534 (by decide +kernel)

theorem valid3_540 : thresholds3_540.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_540 (by decide +kernel)

theorem valid3_546 : thresholds3_546.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_546 (by decide +kernel)

theorem valid3_552 : thresholds3_552.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_552 (by decide +kernel)

theorem valid3_558 : thresholds3_558.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_558 (by decide +kernel)

theorem valid3_564 : thresholds3_564.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_564 (by decide +kernel)

theorem valid3_570 : thresholds3_570.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_570 (by decide +kernel)

theorem valid3_576 : thresholds3_576.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_576 (by decide +kernel)

theorem valid3_582 : thresholds3_582.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_582 (by decide +kernel)

theorem valid3_588 : thresholds3_588.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_588 (by decide +kernel)

theorem valid3_594 : thresholds3_594.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_594 (by decide +kernel)

theorem valid3_600 : thresholds3_600.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_600 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part010

section Pack_Z6970H2307PackedBand03Part011

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid3_606 : thresholds3_606.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_606 (by decide +kernel)

theorem valid3_612 : thresholds3_612.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_612 (by decide +kernel)

theorem valid3_618 : thresholds3_618.all (checked ⟨3,3,1⟩)=true :=
  checkedVerified ⟨3,3,1⟩ prefixMap3 thresholds3_618 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand03Part011

section Pack_Z6970H2307PackedBand04Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_0_0 : (thresholds4_0.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_0.take 4) (by decide +kernel)

private theorem valid4_0_4 : (thresholds4_0.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_0.drop 4) (by decide +kernel)

theorem valid4_0 : thresholds4_0.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_0 4 valid4_0_0 (valid4_0_4)

theorem valid4_6 : thresholds4_6.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_6 (by decide +kernel)

theorem valid4_12 : thresholds4_12.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_12 (by decide +kernel)

theorem valid4_18 : thresholds4_18.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_18 (by decide +kernel)

theorem valid4_24 : thresholds4_24.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_24 (by decide +kernel)

private theorem valid4_30_0 : (thresholds4_30.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_30.take 5) (by decide +kernel)

private theorem valid4_30_5 : (thresholds4_30.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_30.drop 5) (by decide +kernel)

theorem valid4_30 : thresholds4_30.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_30 5 valid4_30_0 (valid4_30_5)

private theorem valid4_36_0 : (thresholds4_36.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_36.take 5) (by decide +kernel)

private theorem valid4_36_5 : (thresholds4_36.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_36.drop 5) (by decide +kernel)

theorem valid4_36 : thresholds4_36.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_36 5 valid4_36_0 (valid4_36_5)

private theorem valid4_42_0 : (thresholds4_42.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_42.take 4) (by decide +kernel)

private theorem valid4_42_4 : (thresholds4_42.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_42.drop 4) (by decide +kernel)

theorem valid4_42 : thresholds4_42.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_42 4 valid4_42_0 (valid4_42_4)

private theorem valid4_48_0 : (thresholds4_48.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_48.take 5) (by decide +kernel)

private theorem valid4_48_5 : (thresholds4_48.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_48.drop 5) (by decide +kernel)

theorem valid4_48 : thresholds4_48.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_48 5 valid4_48_0 (valid4_48_5)

private theorem valid4_54_0 : (thresholds4_54.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_54.take 4) (by decide +kernel)

private theorem valid4_54_4 : (thresholds4_54.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_54.drop 4) (by decide +kernel)

theorem valid4_54 : thresholds4_54.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_54 4 valid4_54_0 (valid4_54_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part000

section Pack_Z6970H2307PackedBand04Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_60_0 : (thresholds4_60.take 2).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_60.take 2) (by decide +kernel)

private theorem valid4_60_2 : ((thresholds4_60.drop 2).take 2).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 ((thresholds4_60.drop 2).take 2) (by decide +kernel)

private theorem valid4_60_4 : (thresholds4_60.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_60.drop 4) (by decide +kernel)

theorem valid4_60 : thresholds4_60.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_60 2 valid4_60_0 (all_take_drop (checked ⟨4,3,1⟩) (thresholds4_60.drop 2) 2 valid4_60_2 (valid4_60_4))

private theorem valid4_66_0 : (thresholds4_66.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_66.take 4) (by decide +kernel)

private theorem valid4_66_4 : (thresholds4_66.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_66.drop 4) (by decide +kernel)

theorem valid4_66 : thresholds4_66.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_66 4 valid4_66_0 (valid4_66_4)

private theorem valid4_72_0 : (thresholds4_72.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_72.take 5) (by decide +kernel)

private theorem valid4_72_5 : (thresholds4_72.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_72.drop 5) (by decide +kernel)

theorem valid4_72 : thresholds4_72.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_72 5 valid4_72_0 (valid4_72_5)

private theorem valid4_78_0 : (thresholds4_78.take 2).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_78.take 2) (by decide +kernel)

private theorem valid4_78_2 : (thresholds4_78.drop 2).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_78.drop 2) (by decide +kernel)

theorem valid4_78 : thresholds4_78.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_78 2 valid4_78_0 (valid4_78_2)

private theorem valid4_84_0 : (thresholds4_84.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_84.take 3) (by decide +kernel)

private theorem valid4_84_3 : (thresholds4_84.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_84.drop 3) (by decide +kernel)

theorem valid4_84 : thresholds4_84.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_84 3 valid4_84_0 (valid4_84_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part001

section Pack_Z6970H2307PackedBand04Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_90_0 : (thresholds4_90.take 1).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_90.take 1) (by decide +kernel)

private theorem valid4_90_1 : ((thresholds4_90.drop 1).take 1).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 ((thresholds4_90.drop 1).take 1) (by decide +kernel)

private theorem valid4_90_2 : ((thresholds4_90.drop 2).take 2).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 ((thresholds4_90.drop 2).take 2) (by decide +kernel)

private theorem valid4_90_4 : (thresholds4_90.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_90.drop 4) (by decide +kernel)

theorem valid4_90 : thresholds4_90.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_90 1 valid4_90_0 (all_take_drop (checked ⟨4,3,1⟩) (thresholds4_90.drop 1) 1 valid4_90_1 (all_take_drop (checked ⟨4,3,1⟩) (thresholds4_90.drop 2) 2 valid4_90_2 (valid4_90_4)))

private theorem valid4_96_0 : (thresholds4_96.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_96.take 4) (by decide +kernel)

private theorem valid4_96_4 : (thresholds4_96.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_96.drop 4) (by decide +kernel)

theorem valid4_96 : thresholds4_96.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_96 4 valid4_96_0 (valid4_96_4)

private theorem valid4_102_0 : (thresholds4_102.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_102.take 3) (by decide +kernel)

private theorem valid4_102_3 : (thresholds4_102.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_102.drop 3) (by decide +kernel)

theorem valid4_102 : thresholds4_102.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_102 3 valid4_102_0 (valid4_102_3)

private theorem valid4_108_0 : (thresholds4_108.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_108.take 4) (by decide +kernel)

private theorem valid4_108_4 : (thresholds4_108.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_108.drop 4) (by decide +kernel)

theorem valid4_108 : thresholds4_108.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_108 4 valid4_108_0 (valid4_108_4)

private theorem valid4_114_0 : (thresholds4_114.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_114.take 5) (by decide +kernel)

private theorem valid4_114_5 : (thresholds4_114.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_114.drop 5) (by decide +kernel)

theorem valid4_114 : thresholds4_114.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_114 5 valid4_114_0 (valid4_114_5)

private theorem valid4_120_0 : (thresholds4_120.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_120.take 3) (by decide +kernel)

private theorem valid4_120_3 : (thresholds4_120.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_120.drop 3) (by decide +kernel)

theorem valid4_120 : thresholds4_120.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_120 3 valid4_120_0 (valid4_120_3)

private theorem valid4_126_0 : (thresholds4_126.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_126.take 5) (by decide +kernel)

private theorem valid4_126_5 : (thresholds4_126.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_126.drop 5) (by decide +kernel)

theorem valid4_126 : thresholds4_126.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_126 5 valid4_126_0 (valid4_126_5)

private theorem valid4_132_0 : (thresholds4_132.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_132.take 4) (by decide +kernel)

private theorem valid4_132_4 : (thresholds4_132.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_132.drop 4) (by decide +kernel)

theorem valid4_132 : thresholds4_132.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_132 4 valid4_132_0 (valid4_132_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part002

section Pack_Z6970H2307PackedBand04Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_138_0 : (thresholds4_138.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_138.take 4) (by decide +kernel)

private theorem valid4_138_4 : (thresholds4_138.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_138.drop 4) (by decide +kernel)

theorem valid4_138 : thresholds4_138.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_138 4 valid4_138_0 (valid4_138_4)

private theorem valid4_144_0 : (thresholds4_144.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_144.take 4) (by decide +kernel)

private theorem valid4_144_4 : (thresholds4_144.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_144.drop 4) (by decide +kernel)

theorem valid4_144 : thresholds4_144.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_144 4 valid4_144_0 (valid4_144_4)

private theorem valid4_150_0 : (thresholds4_150.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_150.take 4) (by decide +kernel)

private theorem valid4_150_4 : (thresholds4_150.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_150.drop 4) (by decide +kernel)

theorem valid4_150 : thresholds4_150.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_150 4 valid4_150_0 (valid4_150_4)

private theorem valid4_156_0 : (thresholds4_156.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_156.take 5) (by decide +kernel)

private theorem valid4_156_5 : (thresholds4_156.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_156.drop 5) (by decide +kernel)

theorem valid4_156 : thresholds4_156.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_156 5 valid4_156_0 (valid4_156_5)

private theorem valid4_162_0 : (thresholds4_162.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_162.take 4) (by decide +kernel)

private theorem valid4_162_4 : (thresholds4_162.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_162.drop 4) (by decide +kernel)

theorem valid4_162 : thresholds4_162.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_162 4 valid4_162_0 (valid4_162_4)

private theorem valid4_168_0 : (thresholds4_168.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_168.take 4) (by decide +kernel)

private theorem valid4_168_4 : (thresholds4_168.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_168.drop 4) (by decide +kernel)

theorem valid4_168 : thresholds4_168.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_168 4 valid4_168_0 (valid4_168_4)

private theorem valid4_174_0 : (thresholds4_174.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_174.take 5) (by decide +kernel)

private theorem valid4_174_5 : (thresholds4_174.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_174.drop 5) (by decide +kernel)

theorem valid4_174 : thresholds4_174.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_174 5 valid4_174_0 (valid4_174_5)

private theorem valid4_180_0 : (thresholds4_180.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_180.take 3) (by decide +kernel)

private theorem valid4_180_3 : (thresholds4_180.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_180.drop 3) (by decide +kernel)

theorem valid4_180 : thresholds4_180.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_180 3 valid4_180_0 (valid4_180_3)

private theorem valid4_186_0 : (thresholds4_186.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_186.take 5) (by decide +kernel)

private theorem valid4_186_5 : (thresholds4_186.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_186.drop 5) (by decide +kernel)

theorem valid4_186 : thresholds4_186.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_186 5 valid4_186_0 (valid4_186_5)

private theorem valid4_192_0 : (thresholds4_192.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_192.take 4) (by decide +kernel)

private theorem valid4_192_4 : (thresholds4_192.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_192.drop 4) (by decide +kernel)

theorem valid4_192 : thresholds4_192.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_192 4 valid4_192_0 (valid4_192_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part003
