import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part1

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At167 : rawChunk w3 167 16 = 192232051765 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 167 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At183 : rawChunk w3 183 16 = 208414391977 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 183 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At199 : rawChunk w3 199 16 = 222883968066 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 199 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
