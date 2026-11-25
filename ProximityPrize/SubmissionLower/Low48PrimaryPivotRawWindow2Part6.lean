import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part1

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At610 : rawChunk w2 610 16 = 537653642183 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 610 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At626 : rawChunk w2 626 16 = 540890557211 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 626 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At642 : rawChunk w2 642 16 = 543869051507 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 642 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
