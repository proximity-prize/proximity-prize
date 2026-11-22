import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At370 : rawChunk w2 370 16 = 415482599923 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 370 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At386 : rawChunk w2 386 16 = 439777509404 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 386 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At402 : rawChunk w2 402 16 = 460501578311 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 402 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
