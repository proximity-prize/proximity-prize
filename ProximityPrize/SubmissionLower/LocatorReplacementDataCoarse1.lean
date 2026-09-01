import ProximityPrize.SubmissionLower.LocatorReplacementDataCore
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_coarse_5:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((5:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_6:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((6:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_7:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((7:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_8:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((8:Fin 17),(yi,ti))):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData

