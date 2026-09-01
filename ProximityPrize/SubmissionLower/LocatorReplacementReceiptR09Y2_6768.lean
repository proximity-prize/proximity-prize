import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y2D_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2:
    ∀ y:Fin 79,40≤y.val→y.val<60→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by
  intro y hlo hhi b
  by_cases h45:y.val<45
  · exact receipt_r09_y2a y hlo h45 b
  by_cases h50:y.val<50
  · exact receipt_r09_y2b y (by omega) h50 b
  by_cases h55:y.val<55
  · exact receipt_r09_y2c y (by omega) h55 b
  · exact receipt_r09_y2d y (by omega) hhi b
end ProximityPrize.SubmissionLower.LocatorReplacementData
