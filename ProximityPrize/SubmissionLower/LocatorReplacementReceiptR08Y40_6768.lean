import ProximityPrize.SubmissionLower.LocatorReplacementData
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y40:∀ b:Fin 160,
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨40,by decide⟩:Fin 79),b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
