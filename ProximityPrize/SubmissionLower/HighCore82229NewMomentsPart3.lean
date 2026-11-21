import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_3 : blockEstimate 6010 1275 1875 200 = 0x3d0ffbdb9a := by decide +kernel
theorem w6010_1275_15 : blockEstimate 6010 1275 4275 200 = 0x1a9bf0aafb8 := by decide +kernel
theorem w6010_1275_27 : blockEstimate 6010 1275 6675 200 = 0xb29b9dba73 := by decide +kernel
theorem w4863_1027_3 : blockEstimate 4863 1027 1627 200 = 0x2fd9a8c4f2 := by decide +kernel
theorem w4863_1027_15 : blockEstimate 4863 1027 4027 200 = 0xda3b4cd2e8 := by decide +kernel
theorem w4863_1027_27 : blockEstimate 4863 1027 6427 200 = 0x8673c4073 := by decide +kernel
theorem w3850_812_17 : blockEstimate 3850 812 4212 200 = 0x3048617aec := by decide +kernel
theorem w3142_664_6 : blockEstimate 3142 664 1864 200 = 0x3727bee840 := by decide +kernel
theorem w3142_664_18 : blockEstimate 3142 664 4264 200 = 0x8729e7fd := by decide +kernel
theorem w2235_472_11 : blockEstimate 2235 472 2672 200 = 0x3e7888d76 := by decide +kernel
theorem w2035_429_9 : blockEstimate 2035 429 2229 200 = 0x6350e2efb := by decide +kernel
theorem w1815_383_9 : blockEstimate 1815 383 2183 200 = 0x1bff52d39 := by decide +kernel
theorem w1202_254_2 : blockEstimate 1202 254 654 200 = 0x31378a4cc := by decide +kernel
theorem w1101_233_4 : blockEstimate 1101 233 1033 200 = 0x1b85cf391 := by decide +kernel
theorem w831_188_0 : blockEstimate 831 188 188 200 = 0x36fc37a7 := by decide +kernel
theorem w731_154_0 : blockEstimate 731 154 154 200 = 0x2e678319 := by decide +kernel
theorem w692_155_3 : blockEstimate 692 155 755 200 = 0x2b0e22ef := by decide +kernel
theorem w522_118_2 : blockEstimate 522 118 518 200 = 0x1b847042 := by decide +kernel
theorem w175_39_0 : blockEstimate 175 39 39 200 = 0x1a38d3b := by decide +kernel
theorem w522_118_3 : blockEstimate 522 118 718 40 = 0x2dbfe0 := by decide +kernel

end HighCore82219BankProof
