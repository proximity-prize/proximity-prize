import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At263 : rawChunk w3 263 16 = 266055677023 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 263 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At279 : rawChunk w3 279 16 = 272560634689 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 279 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At295 : rawChunk w3 295 16 = 275016152716 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 295 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
