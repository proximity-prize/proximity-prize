import ProximityPrize.SubmissionLower.LocatorReplacementReceipt15Chunk2
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_15_y18:∀ ti:Fin 51,
    Receipt ((15:Fin 16),(18:Fin 36),ti):=by decide
theorem receipt_15_y19:∀ ti:Fin 51,
    Receipt ((15:Fin 16),(19:Fin 36),ti):=by decide
theorem receipt_15_y20:∀ ti:Fin 51,
    Receipt ((15:Fin 16),(20:Fin 36),ti):=by decide
theorem receipt_15_y21:∀ ti:Fin 51,
    Receipt ((15:Fin 16),(21:Fin 36),ti):=by decide
theorem receipt_15_y22:∀ ti:Fin 51,
    Receipt ((15:Fin 16),(22:Fin 36),ti):=by decide
theorem receipt_15_y23:∀ ti:Fin 51,
    Receipt ((15:Fin 16),(23:Fin 36),ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
