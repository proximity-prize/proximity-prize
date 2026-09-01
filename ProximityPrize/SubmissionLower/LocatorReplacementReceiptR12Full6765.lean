import ProximityPrize.SubmissionLower.LocatorReplacementData
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r12_full:
    ∀ y:Fin 78,∀ b:Fin 154,
      Receipt ((⟨11,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt_r12_full
