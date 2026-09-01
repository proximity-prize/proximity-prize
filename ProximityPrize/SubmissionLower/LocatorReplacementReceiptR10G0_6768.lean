import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r10_g0:∀ y:Fin 79,y.val<8→∀ b:Fin 160,
    Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
