import ProximityPrize.SubmissionLower.LocatorReplacementDataCore
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_coarse_9:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((9:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_10:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((10:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_11:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((11:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_12:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((12:Fin 17),(yi,ti))):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData

