import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y1A_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y1b:
    ∀ y:Fin 79,25≤y.val→y.val<30→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
