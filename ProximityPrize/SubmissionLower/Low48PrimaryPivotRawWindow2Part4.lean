import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At514 : rawChunk w2 514 16 = 511664793208 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 514 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At530 : rawChunk w2 530 16 = 516891553350 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 530 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At546 : rawChunk w2 546 16 = 521727590227 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 546 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
