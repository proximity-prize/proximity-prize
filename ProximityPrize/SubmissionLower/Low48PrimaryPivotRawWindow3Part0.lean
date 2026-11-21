import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At23 : rawChunk w3 23 16 = 23891751406 :=
  (rawChunk_fast w3 23 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At39 : rawChunk w3 39 16 = 38335177325 :=
  (rawChunk_fast w3 39 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At55 : rawChunk w3 55 16 = 54290025521 :=
  (rawChunk_fast w3 55 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
