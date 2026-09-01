import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR12G5_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r12_g6:∀ y:Fin 79,48≤y.val→y.val<56→∀ b:Fin 160,
    Receipt ((⟨11,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
