import ProximityPrize.SubmissionLower.LocatorReplacementDataBase
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_0:∀ yi:Fin 36,∀ ti:Fin 66,Receipt ((0:Fin 16),yi,ti):=by decide
theorem receipt_1:∀ yi:Fin 36,∀ ti:Fin 66,Receipt ((1:Fin 16),yi,ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
