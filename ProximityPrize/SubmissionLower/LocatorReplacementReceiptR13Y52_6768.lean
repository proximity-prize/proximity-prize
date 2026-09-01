import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR13Y44_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r13_y52:
    ∀ y:Fin 79,52≤y.val→y.val<54→∀ b:Fin 160,
      Receipt ((⟨12,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
