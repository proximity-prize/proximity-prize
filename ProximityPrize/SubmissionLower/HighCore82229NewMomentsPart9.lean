import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb136_30_0 : blockEstimate 136 30 30 166 = 0x9a30e6 := by decide +kernel
theorem nb1687_355_0 : blockEstimate 1687 355 355 800 = 0x12470a8053 := by decide +kernel
theorem nb188_41_0 : blockEstimate 188 41 41 229 = 0x224f886 := by decide +kernel
theorem nb2096_448_0 : blockEstimate 2096 448 448 800 = 0x1b8194c890 := by decide +kernel
theorem nb2179_461_0 : blockEstimate 2179 461 461 800 = 0x1d4a7f9c3b := by decide +kernel
theorem nb371_84_0 : blockEstimate 371 84 84 455 = 0x20c08c09 := by decide +kernel
theorem nb4935_1017_0 : blockEstimate 4935 1017 1017 800 = 0x5677881be8 := by decide +kernel
theorem nb5036_1070_0 : blockEstimate 5036 1070 1070 800 = 0x587b2c19c8 := by decide +kernel
theorem nb595_125_0 : blockEstimate 595 125 125 720 = 0xcaca5052 := by decide +kernel
theorem nb7120_1510_0 : blockEstimate 7120 1510 1510 800 = 0x820aba0748 := by decide +kernel

end HighCore82219BankProof
