import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb108_23_0 : blockEstimate 108 23 23 131 = 0x3ca9b9 := by decide +kernel
theorem nb2179_461_3 : blockEstimate 2179 461 2861 240 = 0x909d6db4 := by decide +kernel
theorem nb2395_500_3 : blockEstimate 2395 500 2900 495 = 0x523575210 := by decide +kernel
theorem nb2479_526_2 : blockEstimate 2479 526 2126 800 = 0x4fda275696 := by decide +kernel
theorem nb3787_799_0 : blockEstimate 3787 799 799 800 = 0x3f92964d68 := by decide +kernel
theorem nb4935_1017_7 : blockEstimate 4935 1017 6617 352 = 0x416be6968 := by decide +kernel
theorem nb6482_1369_2 : blockEstimate 6482 1369 2969 800 = 0x5d3b41a8ff0 := by decide +kernel
theorem nb6482_1369_6 : blockEstimate 6482 1369 6169 800 = 0x5c1f774b42c := by decide +kernel
theorem nb692_155_1 : blockEstimate 692 155 955 47 = 0x61368c := by decide +kernel
theorem nb882_186_1 : blockEstimate 882 186 986 268 = 0x491eb513 := by decide +kernel

end HighCore82219BankProof
