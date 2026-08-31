import ProximityPrize.SubmissionLower.LocatorReplacementReceipt01
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_2:∀ yi:Fin 36,∀ ti:Fin 66,Receipt ((2:Fin 16),yi,ti):=by decide
theorem receipt_3:∀ yi:Fin 36,∀ ti:Fin 66,Receipt ((3:Fin 16),yi,ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
