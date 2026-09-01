import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR14Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r15_g0:∀ y:Fin 79,y.val<8→∀ b:Fin 160,
    Receipt ((⟨14,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
