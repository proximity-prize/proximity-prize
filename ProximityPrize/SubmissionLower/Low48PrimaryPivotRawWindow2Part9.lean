import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At754 : rawChunk w2 754 16 = 558842694990 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 754 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At770 : rawChunk w2 770 16 = 560308956877 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 770 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At786 : rawChunk w2 786 16 = 561642591061 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 786 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
