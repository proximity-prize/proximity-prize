import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR07Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y0:
    ∀ y:Fin 79,y.val<20→∀ b:Fin 160,
      Receipt ((⟨7,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
