import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part9

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At802 : rawChunk w2 802 16 = 562853628080 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 802 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At818 : rawChunk w2 818 16 = 563951564653 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 818 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At834 : rawChunk w2 834 16 = 564945152168 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 834 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
