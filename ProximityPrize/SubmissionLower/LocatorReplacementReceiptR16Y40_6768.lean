import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y32_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r16_y40:
    ∀ y:Fin 79,40≤y.val→y.val<42→∀ b:Fin 160,
      Receipt ((⟨15,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
