import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR14G3_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r14_g4:∀ y:Fin 79,32≤y.val→y.val<40→∀ b:Fin 160,
    Receipt ((⟨13,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
