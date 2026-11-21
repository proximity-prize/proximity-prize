import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1298_273_1 : blockEstimate 1298 273 1073 771 = 0x7766ab143 := by decide +kernel
theorem nb1721_365_1 : blockEstimate 1721 365 1165 800 = 0x20e95eb197 := by decide +kernel
theorem nb244_54_0 : blockEstimate 244 54 54 298 = 0x6176fe9 := by decide +kernel
theorem nb3787_799_3 : blockEstimate 3787 799 3199 800 = 0x159cefd5e5f := by decide +kernel
theorem nb407_89_0 : blockEstimate 407 89 89 496 = 0x2e1859e9 := by decide +kernel
theorem nb5036_1070_7 : blockEstimate 5036 1070 6670 506 = 0xc2c01f0f2 := by decide +kernel
theorem nb7120_1510_10 : blockEstimate 7120 1510 9510 630 = 0x2159bb26ff := by decide +kernel
theorem nb7120_1510_8 : blockEstimate 7120 1510 7910 800 = 0x3a4a8d4a79c := by decide +kernel
theorem nb844_187_0 : blockEstimate 844 187 187 800 = 0x3262ab773 := by decide +kernel

end HighCore82219BankProof
