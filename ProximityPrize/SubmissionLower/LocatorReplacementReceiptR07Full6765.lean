import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR06Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r07_full:
    ∀ y:Fin 79,∀ b:Fin 160,
      Receipt ((⟨6,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt_r07_full
