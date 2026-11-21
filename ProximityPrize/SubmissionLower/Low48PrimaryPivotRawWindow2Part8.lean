import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At706 : rawChunk w2 706 16 = 553537116024 :=
  (rawChunk_fast w2 706 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At722 : rawChunk w2 722 16 = 555468564279 :=
  (rawChunk_fast w2 722 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At738 : rawChunk w2 738 16 = 557233067051 :=
  (rawChunk_fast w2 738 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
