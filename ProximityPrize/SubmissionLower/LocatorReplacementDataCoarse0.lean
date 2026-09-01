import ProximityPrize.SubmissionLower.LocatorReplacementDataCore
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_coarse_0:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((0:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_1:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((1:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_2:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((2:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_3:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((3:Fin 17),(yi,ti))):=by decide
theorem receipt_coarse_4:∀ yi:Fin 20,∀ ti:Fin 20,
    Receipt (Sum.inl ((4:Fin 17),(yi,ti))):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData

