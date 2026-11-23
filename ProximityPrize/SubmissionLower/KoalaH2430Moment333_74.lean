import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p74 : blockEstimate 333 74 74 128 = 0x4ba3467 := by decide +kernel
private theorem p202 : blockEstimate 333 74 202 128 = 0xbcf2500 := by decide +kernel
private theorem p330 : blockEstimate 333 74 330 128 = 0x472c707 := by decide +kernel
private theorem p458 : blockEstimate 333 74 458 23 = 0x6052c := by decide +kernel

theorem moment333_74 : momentEstimate 333 74 = 0x1502259a :=
  moment_from_blocks [⟨128,0x4ba3467⟩, ⟨128,0xbcf2500⟩, ⟨128,0x472c707⟩, ⟨23,0x6052c⟩] ⟨p74, p202, p330, p458, trivial⟩ rfl rfl

end KoalaH2430Banks
