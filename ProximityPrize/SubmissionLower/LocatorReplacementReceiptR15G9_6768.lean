import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR15G8_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r15_g9:∀ y:Fin 79,72≤y.val→∀ b:Fin 160,
    Receipt ((⟨14,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
