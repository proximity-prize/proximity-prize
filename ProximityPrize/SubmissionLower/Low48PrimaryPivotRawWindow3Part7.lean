import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part0

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At359 : rawChunk w3 359 16 = 233527456936 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 359 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At375 : rawChunk w3 375 16 = 219086044712 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 375 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At391 : rawChunk w3 391 16 = 205180598696 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 391 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
