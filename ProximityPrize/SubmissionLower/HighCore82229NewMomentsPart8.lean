import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_8 : blockEstimate 6010 1275 2875 200 = 0x1100f848c38 := by decide +kernel
theorem w6010_1275_20 : blockEstimate 6010 1275 5275 200 = 0x188eae7f238 := by decide +kernel
theorem w6010_1275_32 : blockEstimate 6010 1275 7675 200 = 0x27ecef8535 := by decide +kernel
theorem w4863_1027_8 : blockEstimate 4863 1027 2627 200 = 0xb398850768 := by decide +kernel
theorem w4863_1027_20 : blockEstimate 4863 1027 5027 200 = 0x85b28b51d1 := by decide +kernel
theorem w3850_812_3 : blockEstimate 3850 812 1412 200 = 0x242e7ad71a := by decide +kernel
theorem w3850_812_10 : blockEstimate 3850 812 2812 200 = 0x702b79fa68 := by decide +kernel
theorem w3850_812_22 : blockEstimate 3850 812 5212 200 = 0x14de63b71 := by decide +kernel
theorem w3142_664_14 : blockEstimate 3142 664 3464 200 = 0x185634c830 := by decide +kernel
theorem w2235_472_7 : blockEstimate 2235 472 1872 200 = 0x146953a354 := by decide +kernel
theorem w2035_429_5 : blockEstimate 2035 429 1429 200 = 0x10879d2104 := by decide +kernel
theorem w1815_383_5 : blockEstimate 1815 383 1383 200 = 0xb91fd0b00 := by decide +kernel
theorem w1412_298_6 : blockEstimate 1412 298 1498 200 = 0x2416de927 := by decide +kernel
theorem w1101_233_1 : blockEstimate 1101 233 433 200 = 0x192678834 := by decide +kernel
theorem w892_188_0 : blockEstimate 892 188 188 200 = 0x3be7ad59 := by decide +kernel
theorem w1412_298_8 : blockEstimate 1412 298 1898 110 = 0x95ecb92 := by decide +kernel
theorem w692_155_1 : blockEstimate 692 155 355 200 = 0x9c92b638 := by decide +kernel
theorem w606_128_1 : blockEstimate 606 128 328 200 = 0x6a585290 := by decide +kernel
theorem w148_33_0 : blockEstimate 148 33 33 181 = 0xd8f2fa := by decide +kernel
theorem w347_78_2 : blockEstimate 347 78 478 25 = 0x7ee00 := by decide +kernel

end HighCore82219BankProof
