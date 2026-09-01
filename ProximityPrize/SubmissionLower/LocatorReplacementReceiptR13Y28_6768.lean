import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR13Y20_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r13_y28:
    ∀ y:Fin 79,28≤y.val→y.val<30→∀ b:Fin 160,
      Receipt ((⟨12,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
