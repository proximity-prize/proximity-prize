import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR17Y18_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r17_y26:
    ∀ y:Fin 79,26≤y.val→y.val<28→∀ b:Fin 160,
      Receipt ((⟨16,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
