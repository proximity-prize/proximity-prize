import ProximityPrize.SubmissionLower.LocatorReplacementReceipt45
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
theorem receipt_6 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((6 : Fin 8), yi, ti) := by decide
theorem receipt_7 : ∀ yi : Fin 60, ∀ ti : Fin 57,
    Receipt ((7 : Fin 8), yi, ti) := by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
