import ProximityPrize.SubmissionLower.LocatorReplacementDataBase
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
theorem receipt_0 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((0 : Fin 8), yi, ti) := by decide
theorem receipt_1 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((1 : Fin 8), yi, ti) := by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
