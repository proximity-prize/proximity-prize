-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Moments4.lean.
import ProximityPrize.SubmissionLower.Peer653High53Moments3

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace Peer653High53BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem part3142_664_0 : blockEstimate 3142 664 664 220 = 0x13f4a2ef1 := by decide +kernel
private theorem part3142_664_1 : blockEstimate 3142 664 884 220 = 0x81d304ab5 := by decide +kernel
private theorem part3142_664_2 : blockEstimate 3142 664 1104 220 = 0x144ff225d9 := by decide +kernel
private theorem part3142_664_3 : blockEstimate 3142 664 1324 220 = 0x234cc5c69f := by decide +kernel
private theorem part3142_664_4 : blockEstimate 3142 664 1544 220 = 0x3024f805d0 := by decide +kernel
private theorem part3142_664_5 : blockEstimate 3142 664 1764 220 = 0x39b10e1e70 := by decide +kernel
private theorem part3142_664_6 : blockEstimate 3142 664 1984 220 = 0x3ff107af90 := by decide +kernel
private theorem part3142_664_7 : blockEstimate 3142 664 2204 220 = 0x42e4e4b930 := by decide +kernel
private theorem part3142_664_8 : blockEstimate 3142 664 2424 220 = 0x428ca53b50 := by decide +kernel
private theorem part3142_664_9 : blockEstimate 3142 664 2644 220 = 0x3ee84935f0 := by decide +kernel
private theorem part3142_664_10 : blockEstimate 3142 664 2864 220 = 0x37f7d0a910 := by decide +kernel
private theorem part3142_664_11 : blockEstimate 3142 664 3084 220 = 0x2de5b6fd77 := by decide +kernel
private theorem part3142_664_12 : blockEstimate 3142 664 3304 220 = 0x22732ae669 := by decide +kernel
private theorem part3142_664_13 : blockEstimate 3142 664 3524 220 = 0x175892687f := by decide +kernel
private theorem part3142_664_14 : blockEstimate 3142 664 3744 220 = 0xd8f389de2 := by decide +kernel
private theorem part3142_664_15 : blockEstimate 3142 664 3964 220 = 0x5fb3c5c20 := by decide +kernel
private theorem part3142_664_16 : blockEstimate 3142 664 4184 220 = 0x15e5cf233 := by decide +kernel
private theorem part3142_664_17 : blockEstimate 3142 664 4404 66 = 0x4c06b69 := by decide +kernel
theorem moment3142_664 : momentEstimate 3142 664 = 0x263b0eab16b := by
  exact moment_from_blocks [⟨220,0x13f4a2ef1⟩, ⟨220,0x81d304ab5⟩, ⟨220,0x144ff225d9⟩, ⟨220,0x234cc5c69f⟩, ⟨220,0x3024f805d0⟩, ⟨220,0x39b10e1e70⟩, ⟨220,0x3ff107af90⟩, ⟨220,0x42e4e4b930⟩, ⟨220,0x428ca53b50⟩, ⟨220,0x3ee84935f0⟩, ⟨220,0x37f7d0a910⟩, ⟨220,0x2de5b6fd77⟩, ⟨220,0x22732ae669⟩, ⟨220,0x175892687f⟩, ⟨220,0xd8f389de2⟩, ⟨220,0x5fb3c5c20⟩, ⟨220,0x15e5cf233⟩, ⟨66,0x4c06b69⟩]
    ⟨part3142_664_0, part3142_664_1, part3142_664_2, part3142_664_3, part3142_664_4, part3142_664_5, part3142_664_6, part3142_664_7, part3142_664_8, part3142_664_9, part3142_664_10, part3142_664_11, part3142_664_12, part3142_664_13, part3142_664_14, part3142_664_15, part3142_664_16, part3142_664_17,trivial⟩ rfl rfl


end Peer653High53BankProof
