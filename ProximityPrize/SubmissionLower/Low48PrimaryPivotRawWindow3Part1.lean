import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At71 : rawChunk w3 71 16 = 71706505086 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 71 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At87 : rawChunk w3 87 16 = 90535524189 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 87 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At103 : rawChunk w3 103 16 = 110728689777 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 103 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
