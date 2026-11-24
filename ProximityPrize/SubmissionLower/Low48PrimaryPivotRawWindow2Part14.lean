import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part0

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At994 : rawChunk w2 994 16 = 552786120873 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 994 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At1010 : rawChunk w2 1010 16 = 522665050960 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 1010 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At1026 : rawChunk w2 1026 16 = 492566773771 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 1026 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
