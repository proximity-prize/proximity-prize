import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR17Y58_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r17_y66:
    ∀ y:Fin 79,66≤y.val→y.val<68→∀ b:Fin 160,
      Receipt ((⟨16,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
