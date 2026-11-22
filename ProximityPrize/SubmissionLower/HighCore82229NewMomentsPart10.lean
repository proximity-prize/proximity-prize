import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_10 : blockEstimate 6010 1275 3275 200 = 0x153bcf77d38 := by decide +kernel
theorem w6010_1275_22 : blockEstimate 6010 1275 5675 200 = 0x15a83086338 := by decide +kernel
theorem w6010_1275_34 : blockEstimate 6010 1275 8075 200 = 0xa3d3162ed := by decide +kernel
theorem w4863_1027_10 : blockEstimate 4863 1027 3027 200 = 0xd1c857c868 := by decide +kernel
theorem w4863_1027_22 : blockEstimate 4863 1027 5427 200 = 0x58b6dbe157 := by decide +kernel
theorem w3850_812_5 : blockEstimate 3850 812 1812 200 = 0x4831067268 := by decide +kernel
theorem w3850_812_12 : blockEstimate 3850 812 3212 200 = 0x6af5e57e68 := by decide +kernel
theorem w3142_664_1 : blockEstimate 3142 664 864 200 = 0x62b87191a := by decide +kernel
theorem w3142_664_9 : blockEstimate 3142 664 2464 200 = 0x3c3f0361c0 := by decide +kernel
theorem w2235_472_1 : blockEstimate 2235 472 672 200 = 0x42fb50e72 := by decide +kernel
theorem w4863_1027_29 : blockEstimate 4863 1027 6827 90 = 0x12579959 := by decide +kernel
theorem w2035_429_11 : blockEstimate 2035 429 2629 200 = 0xaeed80a6 := by decide +kernel
theorem w1412_298_1 : blockEstimate 1412 298 498 200 = 0x257f9d1a0 := by decide +kernel
theorem w1202_254_4 : blockEstimate 1202 254 1054 200 = 0x2bdae08d1 := by decide +kernel
theorem w952_201_1 : blockEstimate 952 201 401 200 = 0x1323896bc := by decide +kernel
theorem w831_188_3 : blockEstimate 831 188 788 200 = 0xb83fa15e := by decide +kernel
theorem w706_149_3 : blockEstimate 706 149 749 200 = 0x2fd2f22c := by decide +kernel
theorem w608_128_2 : blockEstimate 608 128 528 200 = 0x47dd1f80 := by decide +kernel
theorem w347_78_1 : blockEstimate 347 78 278 200 = 0xc31102c := by decide +kernel

end HighCore82219BankProof
