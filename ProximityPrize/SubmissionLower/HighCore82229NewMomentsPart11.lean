import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_11 : blockEstimate 6010 1275 3475 200 = 0x16e725bcdb8 := by decide +kernel
theorem w6010_1275_23 : blockEstimate 6010 1275 5875 200 = 0x13c32b14038 := by decide +kernel
theorem w6010_1275_35 : blockEstimate 6010 1275 8275 200 = 0x29b48ec91 := by decide +kernel
theorem w4863_1027_11 : blockEstimate 4863 1027 3227 200 = 0xdb21b050e8 := by decide +kernel
theorem w4863_1027_23 : blockEstimate 4863 1027 5627 200 = 0x43c6c6aa01 := by decide +kernel
theorem w3850_812_6 : blockEstimate 3850 812 2012 200 = 0x563e970268 := by decide +kernel
theorem w3850_812_13 : blockEstimate 3850 812 3412 200 = 0x63d019c268 := by decide +kernel
theorem w3142_664_2 : blockEstimate 3142 664 1064 200 = 0xf91fcb7aa := by decide +kernel
theorem w3142_664_10 : blockEstimate 3142 664 2664 200 = 0x38fd0c8240 := by decide +kernel
theorem w2235_472_2 : blockEstimate 2235 472 872 200 = 0xa1048bfe2 := by decide +kernel
theorem w2035_429_0 : blockEstimate 2035 429 429 200 = 0x981f15e2 := by decide +kernel
theorem w2035_429_10 : blockEstimate 2035 429 2429 200 = 0x2dcf86705 := by decide +kernel
theorem w1412_298_0 : blockEstimate 1412 298 298 200 = 0x65dd5c1a := by decide +kernel
theorem w1202_254_3 : blockEstimate 1202 254 854 200 = 0x361e6288c := by decide +kernel
theorem w952_201_0 : blockEstimate 952 201 201 200 = 0x40c1c97a := by decide +kernel
theorem w831_188_2 : blockEstimate 831 188 588 200 = 0x1281995dc := by decide +kernel
theorem w706_149_2 : blockEstimate 706 149 549 200 = 0x9786cb92 := by decide +kernel
theorem w608_128_1 : blockEstimate 608 128 328 200 = 0x6b128818 := by decide +kernel
theorem w606_128_3 : blockEstimate 606 128 728 134 = 0x6b82424 := by decide +kernel
theorem w175_39_1 : blockEstimate 175 39 239 14 = 0xcb6a := by decide +kernel

end HighCore82219BankProof
