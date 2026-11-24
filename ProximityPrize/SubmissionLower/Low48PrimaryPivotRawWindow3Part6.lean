import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part0

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At311 : rawChunk w3 311 16 = 275634773911 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 311 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At327 : rawChunk w3 327 16 = 264001764333 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 327 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At343 : rawChunk w3 343 16 = 248512355624 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 343 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
