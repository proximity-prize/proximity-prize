import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_0 : blockEstimate 6010 1275 1275 200 = 0x1d8c7c8ea := by decide +kernel
theorem w6010_1275_12 : blockEstimate 6010 1275 3675 200 = 0x18466dcae38 := by decide +kernel
theorem w6010_1275_24 : blockEstimate 6010 1275 6075 200 = 0x11a6fa3c389 := by decide +kernel
theorem w4863_1027_0 : blockEstimate 4863 1027 1027 200 = 0x17c40ce82 := by decide +kernel
theorem w4863_1027_12 : blockEstimate 4863 1027 3427 200 = 0xe0a6a84968 := by decide +kernel
theorem w4863_1027_24 : blockEstimate 4863 1027 5827 200 = 0x30ad835e00 := by decide +kernel
theorem w3850_812_14 : blockEstimate 3850 812 3612 200 = 0x59a2f7b268 := by decide +kernel
theorem w3142_664_3 : blockEstimate 3142 664 1264 200 = 0x1bcb50b6d0 := by decide +kernel
theorem w3142_664_15 : blockEstimate 3142 664 3664 200 = 0xfc3312665 := by decide +kernel
theorem w2235_472_8 : blockEstimate 2235 472 2072 200 = 0x11339142ef := by decide +kernel
theorem w2035_429_6 : blockEstimate 2035 429 1629 200 = 0xfed523a44 := by decide +kernel
theorem w1815_383_6 : blockEstimate 1815 383 1583 200 = 0xa29ba7b00 := by decide +kernel
theorem w1412_298_7 : blockEstimate 1412 298 1698 200 = 0xb4e2900d := by decide +kernel
theorem w1101_233_5 : blockEstimate 1101 233 1233 200 = 0xa34f3186 := by decide +kernel
theorem w831_188_1 : blockEstimate 831 188 388 200 = 0xefc6079c := by decide +kernel
theorem w706_149_1 : blockEstimate 706 149 349 200 = 0x9e507334 := by decide +kernel
theorem w608_128_0 : blockEstimate 608 128 128 200 = 0x236cfeb8 := by decide +kernel
theorem w608_128_3 : blockEstimate 608 128 728 136 = 0x708d6e2 := by decide +kernel
theorem w1202_254_7 : blockEstimate 1202 254 1654 56 = 0x11c3ad0 := by decide +kernel

end HighCore82219BankProof
