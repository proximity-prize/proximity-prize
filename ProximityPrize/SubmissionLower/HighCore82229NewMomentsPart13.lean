import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nb1721_365_2 : blockEstimate 1721 365 1965 486 = 0x3584f56eb := by decide +kernel
theorem nb2096_439_0 : blockEstimate 2096 439 439 800 = 0x1b5154d0e6 := by decide +kernel
theorem nb268_58_0 : blockEstimate 268 58 58 326 = 0x8b05777 := by decide +kernel
theorem nb3244_683_0 : blockEstimate 3244 683 683 800 = 0x3497065989 := by decide +kernel
theorem nb3244_683_3 : blockEstimate 3244 683 3083 800 = 0x91697e5722 := by decide +kernel
theorem nb380_84_0 : blockEstimate 380 84 84 464 = 0x235f32c1 := by decide +kernel
theorem nb6482_1369_1 : blockEstimate 6482 1369 2169 800 = 0x2d1906a42b2 := by decide +kernel
theorem nb6482_1369_5 : blockEstimate 6482 1369 5369 800 = 0x7a923157bf0 := by decide +kernel
theorem nb975_205_0 : blockEstimate 975 205 205 800 = 0x4d7e8243c := by decide +kernel

end HighCore82219BankProof
