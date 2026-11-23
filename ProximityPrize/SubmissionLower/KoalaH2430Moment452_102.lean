import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p102 : blockEstimate 452 102 102 128 = 0x78cb831 := by decide +kernel
private theorem p230 : blockEstimate 452 102 230 128 = 0x1be4b240 := by decide +kernel
private theorem p358 : blockEstimate 452 102 358 128 = 0x1b0bd35e := by decide +kernel
private theorem p486 : blockEstimate 452 102 486 128 = 0x9069a3d := by decide +kernel
private theorem p614 : blockEstimate 452 102 614 42 = 0x2d4664 := by decide +kernel

theorem moment452_102 : momentEstimate 452 102 = 0x47b11e70 :=
  moment_from_blocks [⟨128,0x78cb831⟩, ⟨128,0x1be4b240⟩, ⟨128,0x1b0bd35e⟩, ⟨128,0x9069a3d⟩, ⟨42,0x2d4664⟩] ⟨p102, p230, p358, p486, p614, trivial⟩ rfl rfl

end KoalaH2430Banks
