import ProximityPrize.SubmissionLower.LocatorReplacementReceipt23
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
theorem receipt_4 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((4 : Fin 8), yi, ti) := by decide
theorem receipt_5 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((5 : Fin 8), yi, ti) := by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
