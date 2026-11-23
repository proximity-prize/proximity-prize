import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p159 : blockEstimate 715 159 159 128 = 0xd3734a0 := by decide +kernel
private theorem p287 : blockEstimate 715 159 287 128 = 0x46b754a8 := by decide +kernel
private theorem p415 : blockEstimate 715 159 415 128 = 0x72af7400 := by decide +kernel
private theorem p543 : blockEstimate 715 159 543 128 = 0x76d37400 := by decide +kernel
private theorem p671 : blockEstimate 715 159 671 128 = 0x546de86e := by decide +kernel
private theorem p799 : blockEstimate 715 159 799 128 = 0x22e48dcb := by decide +kernel
private theorem p927 : blockEstimate 715 159 927 106 = 0x41bdc4f := by decide +kernel

theorem moment715_159 : momentEstimate 715 159 = 0x1b8dfc3d0 :=
  moment_from_blocks [⟨128,0xd3734a0⟩, ⟨128,0x46b754a8⟩, ⟨128,0x72af7400⟩, ⟨128,0x76d37400⟩, ⟨128,0x546de86e⟩, ⟨128,0x22e48dcb⟩, ⟨106,0x41bdc4f⟩] ⟨p159, p287, p415, p543, p671, p799, p927, trivial⟩ rfl rfl

end KoalaH2430Banks
