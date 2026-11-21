import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At322 : rawChunk w2 322 16 = 334716499936 :=
  (rawChunk_fast w2 322 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At338 : rawChunk w2 338 16 = 362914994745 :=
  (rawChunk_fast w2 338 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At354 : rawChunk w2 354 16 = 389882069846 :=
  (rawChunk_fast w2 354 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
