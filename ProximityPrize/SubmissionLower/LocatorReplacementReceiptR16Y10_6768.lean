import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y2_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r16_y10:
    ∀ y:Fin 79,10≤y.val→y.val<12→∀ b:Fin 160,
      Receipt ((⟨15,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
