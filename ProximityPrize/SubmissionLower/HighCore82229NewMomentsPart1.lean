import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_1 : blockEstimate 6010 1275 1475 200 = 0xc714b037a := by decide +kernel
theorem w6010_1275_13 : blockEstimate 6010 1275 3875 200 = 0x1959a7a1eb8 := by decide +kernel
theorem w6010_1275_25 : blockEstimate 6010 1275 6275 200 = 0xf7a8dddb16 := by decide +kernel
theorem w4863_1027_1 : blockEstimate 4863 1027 1227 200 = 0x9ef195052 := by decide +kernel
theorem w4863_1027_13 : blockEstimate 4863 1027 3627 200 = 0xe2573fb1e8 := by decide +kernel
theorem w4863_1027_25 : blockEstimate 4863 1027 6027 200 = 0x1fffec09db := by decide +kernel
theorem w3850_812_15 : blockEstimate 3850 812 3812 200 = 0x4ca1c57f71 := by decide +kernel
theorem w3142_664_4 : blockEstimate 3142 664 1464 200 = 0x275fef0340 := by decide +kernel
theorem w3142_664_16 : blockEstimate 3142 664 3864 200 = 0x88f160d95 := by decide +kernel
theorem w2235_472_9 : blockEstimate 2235 472 2272 200 = 0xca0b9de54 := by decide +kernel
theorem w2035_429_7 : blockEstimate 2035 429 1829 200 = 0xdb8f2db84 := by decide +kernel
theorem w1815_383_7 : blockEstimate 1815 383 1783 200 = 0x7708b2634 := by decide +kernel
theorem w1202_254_0 : blockEstimate 1202 254 254 200 = 0x54ec992a := by decide +kernel
theorem w1101_233_2 : blockEstimate 1101 233 633 200 = 0x27b02443c := by decide +kernel
theorem w892_188_3 : blockEstimate 892 188 788 200 = 0x1024e35f2 := by decide +kernel
theorem w952_201_5 : blockEstimate 952 201 1201 153 = 0x1022e2af := by decide +kernel
theorem w2035_429_12 : blockEstimate 2035 429 2829 64 = 0x2cc60b0 := by decide +kernel
theorem w522_118_0 : blockEstimate 522 118 118 200 = 0x1c30de3b := by decide +kernel
theorem w247_55_0 : blockEstimate 247 55 55 200 = 0x5597b9e := by decide +kernel

end HighCore82219BankProof
