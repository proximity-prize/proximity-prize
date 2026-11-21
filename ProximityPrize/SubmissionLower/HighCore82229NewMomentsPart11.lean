import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1106_244_1 : blockEstimate 1106 244 1044 550 = 0x29fdf7e56 := by decide +kernel
theorem nb1307_276_0 : blockEstimate 1307 276 276 800 = 0xa8cb5b995 := by decide +kernel
theorem nb2096_448_3 : blockEstimate 2096 448 2848 144 = 0x1f0b1e18 := by decide +kernel
theorem nb2479_526_3 : blockEstimate 2479 526 2926 605 = 0x97f645466 := by decide +kernel
theorem nb3787_799_1 : blockEstimate 3787 799 1599 800 = 0x12ce46fc900 := by decide +kernel
theorem nb3787_799_5 : blockEstimate 3787 799 4799 586 = 0xdd250536b := by decide +kernel
theorem nb6482_1369_3 : blockEstimate 6482 1369 3769 800 = 0x7b6d09833f0 := by decide +kernel
theorem nb6482_1369_7 : blockEstimate 6482 1369 6969 800 = 0x34a8b6a3387 := by decide +kernel
theorem nb683_143_1 : blockEstimate 683 143 943 26 = 0x11b6fd := by decide +kernel

end HighCore82219BankProof
