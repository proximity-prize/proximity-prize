import ProximityPrize.SubmissionLower.LocatorReplacementReceiptCoarse15
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_fine:∀ c:FineCell,Receipt (Sum.inr (Sum.inl c)):=by decide

end ProximityPrize.SubmissionLower.LocatorReplacementData
