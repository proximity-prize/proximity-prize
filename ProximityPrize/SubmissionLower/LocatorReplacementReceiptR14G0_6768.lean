import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR13Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r14_g0:∀ y:Fin 79,y.val<8→∀ b:Fin 160,
    Receipt ((⟨13,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
