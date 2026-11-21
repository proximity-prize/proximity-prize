import ProximityPrize.SubmissionLower.HighCore82219Moments2

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000
open private r1E r1F from ProximityPrize.SubmissionLower.HighCore82229LegacyMoments


theorem moment4830_1019 : momentEstimate 4830 1019 = 0xd5013df2ef9 := P1_7_1_3_5.moment4830

theorem moment5798_1223 : momentEstimate 5798 1223 = 0x1ba1a89b2ba1 := P1_7_1_3_5.moment5798

theorem moment7630_1607 : momentEstimate 7630 1607 = 0x52bdbe618ec3 := P1_7_1_3_5.moment7630

end HighCore82219BankProof
