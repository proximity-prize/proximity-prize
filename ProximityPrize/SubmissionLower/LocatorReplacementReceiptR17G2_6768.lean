import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR17G1_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r17_g2:∀ y:Fin 79,16≤y.val→y.val<24→∀ b:Fin 160,
    Receipt ((⟨16,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
