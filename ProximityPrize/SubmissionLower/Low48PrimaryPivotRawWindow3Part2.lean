import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At119 : rawChunk w3 119 16 = 132236451901 :=
  (rawChunk_fast w3 119 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At135 : rawChunk w3 135 16 = 154131600028 :=
  (rawChunk_fast w3 135 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At151 : rawChunk w3 151 16 = 174192471414 :=
  (rawChunk_fast w3 151 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
