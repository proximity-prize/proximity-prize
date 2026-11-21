import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At658 : rawChunk w2 658 16 = 546606827619 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 658 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At674 : rawChunk w2 674 16 = 549120493097 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 674 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At690 : rawChunk w2 690 16 = 551425702040 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 690 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
