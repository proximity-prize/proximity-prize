import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At466 : rawChunk w2 466 16 = 493358203126 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 466 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At482 : rawChunk w2 482 16 = 499928099140 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 482 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At498 : rawChunk w2 498 16 = 506019959419 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 498 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
