import ProximityPrize.SubmissionLower.Low48PrimaryRawFastSum

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw2At850 : rawChunk w2 850 16 = 565842725407 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 850 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At866 : rawChunk w2 866 16 = 566652000261 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 866 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw2At882 : rawChunk w2 882 16 = 567380193284 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w2 882 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt
