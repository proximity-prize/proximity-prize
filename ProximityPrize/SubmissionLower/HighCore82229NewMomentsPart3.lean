import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1835_388_1 : blockEstimate 1835 388 1188 800 = 0x2a913f2759 := by decide +kernel
theorem nb1835_388_2 : blockEstimate 1835 388 1988 623 = 0x73541c798 := by decide +kernel
theorem nb2479_526_0 : blockEstimate 2479 526 526 800 = 0x2417951074 := by decide +kernel
theorem nb4935_1017_6 : blockEstimate 4935 1017 5817 800 = 0x7eb8c5ab75 := by decide +kernel
theorem nb5036_1070_6 : blockEstimate 5036 1070 5870 800 = 0xb35cfdb4e9 := by decide +kernel
theorem nb683_143_0 : blockEstimate 683 143 143 800 = 0x15e736c4f := by decide +kernel
theorem nb7120_1510_6 : blockEstimate 7120 1510 6310 800 = 0x953dafaa7d0 := by decide +kernel
theorem nb911_204_1 : blockEstimate 911 204 1004 315 = 0x77108589 := by decide +kernel

end HighCore82219BankProof
