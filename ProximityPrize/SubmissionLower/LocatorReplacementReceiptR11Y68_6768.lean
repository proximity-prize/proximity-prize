import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR11Y60_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r11_y68:
    ∀ y:Fin 79,68≤y.val→y.val<70→∀ b:Fin 160,
      Receipt ((⟨10,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
