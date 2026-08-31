import ProximityPrize.SubmissionLower.LocatorReplacementReceipt4
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_5:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((5:Fin 16),yi,ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
