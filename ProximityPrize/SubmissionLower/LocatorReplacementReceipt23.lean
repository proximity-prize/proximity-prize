import ProximityPrize.SubmissionLower.LocatorReplacementReceipt01
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
theorem receipt_2 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((2 : Fin 8), yi, ti) := by decide
theorem receipt_3 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((3 : Fin 8), yi, ti) := by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
