import ProximityPrize.SubmissionLower.LocatorReplacementPredicates
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_0:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((0:Fin 16),yi,ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
