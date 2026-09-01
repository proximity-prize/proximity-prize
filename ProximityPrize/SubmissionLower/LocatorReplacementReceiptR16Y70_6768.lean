import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y62_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r16_y70:
    ∀ y:Fin 79,70≤y.val→y.val<72→∀ b:Fin 160,
      Receipt ((⟨15,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
