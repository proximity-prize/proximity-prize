import ProximityPrize.SubmissionLower.LocatorReplacementDataCore
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_coarse_13:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((13:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_14:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((14:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_15:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((15:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_16:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((16:Fin 17),(yi,ti))):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData

