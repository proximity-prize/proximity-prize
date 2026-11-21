import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1106_244_0 : blockEstimate 1106 244 244 800 = 0x722762e9b := by decide +kernel
theorem nb2096_439_1 : blockEstimate 2096 439 1239 800 = 0x43b4f722c0 := by decide +kernel
theorem nb2096_439_3 : blockEstimate 2096 439 2839 135 = 0x19af4dfa := by decide +kernel
theorem nb3244_683_1 : blockEstimate 3244 683 1483 800 = 0xd8f4f51860 := by decide +kernel
theorem nb3787_799_4 : blockEstimate 3787 799 3999 800 = 0x920e1e2632 := by decide +kernel
theorem nb6482_1369_9 : blockEstimate 6482 1369 8569 651 = 0x214c2d05f8 := by decide +kernel
theorem nb7120_1510_7 : blockEstimate 7120 1510 7110 800 = 0x696ba27d4bd := by decide +kernel
theorem nb882_186_0 : blockEstimate 882 186 186 800 = 0x38862d1b4 := by decide +kernel

end HighCore82219BankProof
