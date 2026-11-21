import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At407 : rawChunk w3 407 2 = 24696165031 :=
  (rawChunk_fast w3 407 2 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
