import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At562 : rawChunk w2 562 16 = 526198452415 :=
  (rawChunk_fast w2 562 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At578 : rawChunk w2 578 16 = 530328266921 :=
  (rawChunk_fast w2 578 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At594 : rawChunk w2 594 16 = 534139588694 :=
  (rawChunk_fast w2 594 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
