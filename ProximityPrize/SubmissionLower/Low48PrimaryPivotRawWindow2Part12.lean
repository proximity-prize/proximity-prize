import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At898 : rawChunk w2 898 16 = 568034115188 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 898 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At914 : rawChunk w2 914 16 = 568619966791 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 914 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At930 : rawChunk w2 930 16 = 569143694290 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 930 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
