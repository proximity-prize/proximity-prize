import ProximityPrize.SubmissionLower.LocatorReplacementData
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r01_full:
    ∀ y:Fin 79,∀ b:Fin 160,
      Receipt ((⟨0,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt_r01_full
