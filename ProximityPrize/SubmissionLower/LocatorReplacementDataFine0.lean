import ProximityPrize.SubmissionLower.LocatorReplacementDataCore
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_fine_le8:∀ c:FineCell,fineR c≤8→
    Receipt (Sum.inr (Sum.inl c)):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData

