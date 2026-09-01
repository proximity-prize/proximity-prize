import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR10Y22_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r10_y30:
    ∀ y:Fin 79,30≤y.val→y.val<32→∀ b:Fin 160,
      Receipt ((⟨9,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
