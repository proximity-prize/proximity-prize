import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_2 : blockEstimate 6010 1275 1675 200 = 0x208dba6f0a := by decide +kernel
theorem w6010_1275_14 : blockEstimate 6010 1275 4075 200 = 0x1a20d341f38 := by decide +kernel
theorem w6010_1275_26 : blockEstimate 6010 1275 6475 200 = 0xd4ce07ef24 := by decide +kernel
theorem w4863_1027_2 : blockEstimate 4863 1027 1427 200 = 0x19c2ef5d22 := by decide +kernel
theorem w4863_1027_14 : blockEstimate 4863 1027 3827 200 = 0xe033768a68 := by decide +kernel
theorem w4863_1027_26 : blockEstimate 4863 1027 6227 200 = 0x1273e91a3f := by decide +kernel
theorem w3850_812_16 : blockEstimate 3850 812 4012 200 = 0x3e6b976415 := by decide +kernel
theorem w3142_664_5 : blockEstimate 3142 664 1664 200 = 0x3080efb7c0 := by decide +kernel
theorem w3142_664_17 : blockEstimate 3142 664 4064 200 = 0x359231421 := by decide +kernel
theorem w2235_472_10 : blockEstimate 2235 472 2472 200 = 0x7ef8d4fda := by decide +kernel
theorem w2035_429_8 : blockEstimate 2035 429 2029 200 = 0xa1d3f5d3f := by decide +kernel
theorem w1815_383_8 : blockEstimate 1815 383 1983 200 = 0x45655abca := by decide +kernel
theorem w1202_254_1 : blockEstimate 1202 254 454 200 = 0x1d3672e3b := by decide +kernel
theorem w1101_233_3 : blockEstimate 1101 233 833 200 = 0x284c5a7fc := by decide +kernel
theorem w892_188_4 : blockEstimate 892 188 988 200 = 0x5164f0f2 := by decide +kernel
theorem w706_149_0 : blockEstimate 706 149 149 200 = 0x2c3a7ac9 := by decide +kernel
theorem w686_144_1 : blockEstimate 686 144 344 200 = 0x92e4f330 := by decide +kernel
theorem w478_108_0 : blockEstimate 478 108 108 200 = 0x18301ae9 := by decide +kernel
theorem w347_78_0 : blockEstimate 347 78 78 200 = 0xcbdd878 := by decide +kernel

end HighCore82219BankProof
