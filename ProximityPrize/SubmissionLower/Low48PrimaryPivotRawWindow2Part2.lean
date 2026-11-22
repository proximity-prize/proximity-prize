import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At418 : rawChunk w2 418 16 = 470438054203 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 418 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At434 : rawChunk w2 434 16 = 478649930932 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 434 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At450 : rawChunk w2 450 16 = 486277285233 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 450 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
