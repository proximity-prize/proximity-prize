import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR13G0_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r13_g1:∀ y:Fin 79,8≤y.val→y.val<16→∀ b:Fin 160,
    Receipt ((⟨12,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
