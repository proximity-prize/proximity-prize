import ProximityPrize.SubmissionLower.LocatorReplacementReceipt3
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_4:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((4:Fin 16),yi,ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
