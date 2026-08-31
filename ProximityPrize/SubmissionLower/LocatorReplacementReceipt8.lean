import ProximityPrize.SubmissionLower.LocatorReplacementReceipt7
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_8:∀ yi:Fin 36,∀ ti:Fin 51,
    Receipt ((8:Fin 16),yi,ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
