import ProximityPrize.SubmissionLower.LocatorReplacementData
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y2:
    ∀ y:Fin 79,40≤y.val→y.val<60→∀ b:Fin 160,
      Receipt ((⟨8,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
