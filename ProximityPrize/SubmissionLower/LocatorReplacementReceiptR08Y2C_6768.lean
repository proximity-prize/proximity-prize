import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y2B_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y2c:
    ∀ y:Fin 79,50≤y.val→y.val<55→∀ b:Fin 160,
      Receipt ((⟨7,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
