import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1298_273_0 : blockEstimate 1298 273 273 800 = 0xa5afe1bdc := by decide +kernel
theorem nb2096_439_2 : blockEstimate 2096 439 2039 800 = 0x19542c83d9 := by decide +kernel
theorem nb2479_526_1 : blockEstimate 2479 526 1326 800 = 0x70832c9f40 := by decide +kernel
theorem nb3244_683_2 : blockEstimate 3244 683 2283 800 = 0x1003fa0a060 := by decide +kernel
theorem nb552_121_0 : blockEstimate 552 121 121 673 = 0x9b6be4a3 := by decide +kernel
theorem nb6482_1369_0 : blockEstimate 6482 1369 1369 800 = 0x7551830808 := by decide +kernel
theorem nb692_155_0 : blockEstimate 692 155 155 800 = 0x184c20cf7 := by decide +kernel
theorem nb7120_1510_9 : blockEstimate 7120 1510 8710 800 = 0x14dc6cf497c := by decide +kernel

end HighCore82219BankProof
