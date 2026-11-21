import ProximityPrize.SubmissionLower.HighCore82219Moments0

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
open scoped P1_7_1_3_2
set_option maxHeartbeats 14000000


theorem moment1183_249 : momentEstimate 1183 249 = 0xc4f2a7606 := P1_7_1_3_3.moment1183_249

theorem moment1324_279 : momentEstimate 1324 279 = 0x1350bb1fb5 := P1_7_1_3_3.moment1324_279

theorem moment1443_329 : momentEstimate 1443 329 = 0x1cf53a5560 := P1_7_1_3_3.moment1443_329

theorem moment1550_329 : momentEstimate 1550 329 = 0x2473d5ffe4 := P1_7_1_3_3.moment1550_329

theorem moment1696_357 : momentEstimate 1696 357 = 0x33e3754396 := P1_7_1_3_3.moment1696_357

theorem moment1725_359 : momentEstimate 1725 359 = 0x370899d961 := P1_7_1_3_3.moment1725_359

end HighCore82219BankProof
