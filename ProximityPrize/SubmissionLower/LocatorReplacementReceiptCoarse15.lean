import ProximityPrize.SubmissionLower.LocatorReplacementReceiptCoarseBarrier02
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_coarse_15:∀ yi:Fin 19,∀ ti:Fin 19,
    Receipt (Sum.inl ((15:Fin 16),(yi,ti))):=by decide

end ProximityPrize.SubmissionLower.LocatorReplacementData
