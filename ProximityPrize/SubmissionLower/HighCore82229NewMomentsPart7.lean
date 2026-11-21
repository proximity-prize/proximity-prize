import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb151_33_0 : blockEstimate 151 33 33 184 = 0xe74c1b := by decide +kernel
theorem nb1721_365_0 : blockEstimate 1721 365 365 800 = 0x13147e347b := by decide +kernel
theorem nb173_38_0 : blockEstimate 173 38 38 211 = 0x18d4b08 := by decide +kernel
theorem nb2096_448_2 : blockEstimate 2096 448 2048 800 = 0x19ff19b531 := by decide +kernel
theorem nb2179_461_2 : blockEstimate 2179 461 2061 800 = 0x22c2132952 := by decide +kernel
theorem nb392_88_0 : blockEstimate 392 88 88 480 = 0x2881bf10 := by decide +kernel
theorem nb4935_1017_2 : blockEstimate 4935 1017 2617 800 = 0x3345dcbf9f0 := by decide +kernel
theorem nb5036_1070_2 : blockEstimate 5036 1070 2670 800 = 0x36d160b1e50 := by decide +kernel
theorem nb562_118_0 : blockEstimate 562 118 118 680 = 0xa178c6a5 := by decide +kernel
theorem nb7120_1510_2 : blockEstimate 7120 1510 3110 800 = 0x6f3eec657d0 := by decide +kernel

end HighCore82219BankProof
