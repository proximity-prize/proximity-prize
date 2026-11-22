import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At562 : rawChunk w2 562 16 = 526198452415 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 562 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At578 : rawChunk w2 578 16 = 530328266921 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 578 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At594 : rawChunk w2 594 16 = 534139588694 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 594 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
