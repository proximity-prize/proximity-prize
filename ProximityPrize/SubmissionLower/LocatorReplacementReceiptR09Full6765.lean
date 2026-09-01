import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y0_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y1_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y2_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y3_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_full:
    ∀ y:Fin 79,∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y b
  by_cases h0:y.val<20
  · exact receipt_r09_y0 y h0 b
  by_cases h1:y.val<40
  · exact receipt_r09_y1 y (by omega) h1 b
  by_cases h2:y.val<60
  · exact receipt_r09_y2 y (by omega) h2 b
  exact receipt_r09_y3 y (by omega) b
end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt_r09_full
