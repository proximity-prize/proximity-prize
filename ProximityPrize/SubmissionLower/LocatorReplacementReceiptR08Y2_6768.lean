import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y2A_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y2B_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y2C_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y2D_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y2:
    ∀ y:Fin 79,40≤y.val→y.val<60→∀ b:Fin 160,
      Receipt ((⟨7,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  by_cases h0:y.val<45
  · exact receipt_r08_y2a y hlo h0 b
  by_cases h1:y.val<50
  · exact receipt_r08_y2b y (by omega) h1 b
  by_cases h2:y.val<55
  · exact receipt_r08_y2c y (by omega) h2 b
  exact receipt_r08_y2d y (by omega) hhi b
end ProximityPrize.SubmissionLower.LocatorReplacementData
