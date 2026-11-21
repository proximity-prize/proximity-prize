import ProximityPrize.SubmissionLower.AnchorCuts82170Defs

set_option maxRecDepth 28000
set_option maxHeartbeats 3000000
set_option Elab.async false

namespace AnchorCuts82170
open K1_13 K1_13_1_1 SoundnessAnchor AnchorSpace82170

def cuts120 : List (Cut 120) := [
  certify 120 0 84 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 1 127 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 2 139 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 3 130 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 4 114 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 5 98 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 6 82 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 7 67 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 8 53 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 9 41 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 10 31 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 11 23 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 12 16 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 13 11 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 14 7 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 15 4 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 16 2 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel),
  certify 120 17 1 ⟨⟨0,0,0,0⟩,0⟩ (by decide +kernel)]

end AnchorCuts82170
