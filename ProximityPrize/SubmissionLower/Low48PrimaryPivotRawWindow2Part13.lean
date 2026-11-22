import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At946 : rawChunk w2 946 16 = 569610747672 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 946 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At962 : rawChunk w2 962 16 = 570026191178 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 962 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At978 : rawChunk w2 978 16 = 570277136546 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 978 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
