import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part1

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At215 : rawChunk w3 215 16 = 235770137741 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 215 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At231 : rawChunk w3 231 16 = 247190188765 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 231 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At247 : rawChunk w3 247 16 = 257251991908 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 247 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
