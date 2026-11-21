import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb112_24_0 : blockEstimate 112 24 24 136 = 0x464bcb := by decide +kernel
theorem nb1235_261_1 : blockEstimate 1235 261 1061 696 = 0x572e15b4e := by decide +kernel
theorem nb1835_388_0 : blockEstimate 1835 388 388 800 = 0x158dfc55b9 := by decide +kernel
theorem nb213_47_0 : blockEstimate 213 47 47 260 = 0x38bfb68 := by decide +kernel
theorem nb3244_683_4 : blockEstimate 3244 683 3883 727 = 0x15c79e459d := by decide +kernel
theorem nb3787_799_2 : blockEstimate 3787 799 2399 800 = 0x1a27e070900 := by decide +kernel
theorem nb415_91_0 : blockEstimate 415 91 91 506 = 0x31e9f423 := by decide +kernel
theorem nb6482_1369_4 : blockEstimate 6482 1369 4569 800 = 0x8534aebd7f0 := by decide +kernel
theorem nb6482_1369_8 : blockEstimate 6482 1369 7769 800 = 0x137a7937937 := by decide +kernel
theorem nb911_204_0 : blockEstimate 911 204 204 800 = 0x4162e7bdc := by decide +kernel

end HighCore82219BankProof
