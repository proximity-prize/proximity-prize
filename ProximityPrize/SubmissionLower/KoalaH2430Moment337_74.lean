import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem p74 : blockEstimate 337 74 74 128 = 0x4ce707b := by decide +kernel
private theorem p202 : blockEstimate 337 74 202 128 = 0xc2a4200 := by decide +kernel
private theorem p330 : blockEstimate 337 74 330 128 = 0x4d1e45c := by decide +kernel
private theorem p458 : blockEstimate 337 74 458 27 = 0x98bcb := by decide +kernel

theorem moment337_74 : momentEstimate 337 74 = 0x15d422a2 :=
  moment_from_blocks [⟨128,0x4ce707b⟩, ⟨128,0xc2a4200⟩, ⟨128,0x4d1e45c⟩, ⟨27,0x98bcb⟩] ⟨p74, p202, p330, p458, trivial⟩ rfl rfl

end KoalaH2430Banks
