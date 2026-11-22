import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part14

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At1042 : rawChunk w2 1042 16 = 463246686475 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 1042 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At1058 : rawChunk w2 1058 5 = 138889514525 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 1058 5 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
