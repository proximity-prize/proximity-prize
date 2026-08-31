import ProximityPrize.SubmissionLower.LocatorReplacementReceipt13Chunk1
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_13_y12:∀ ti:Fin 51,
    Receipt ((13:Fin 16),(12:Fin 36),ti):=by decide
theorem receipt_13_y13:∀ ti:Fin 51,
    Receipt ((13:Fin 16),(13:Fin 36),ti):=by decide
theorem receipt_13_y14:∀ ti:Fin 51,
    Receipt ((13:Fin 16),(14:Fin 36),ti):=by decide
theorem receipt_13_y15:∀ ti:Fin 51,
    Receipt ((13:Fin 16),(15:Fin 36),ti):=by decide
theorem receipt_13_y16:∀ ti:Fin 51,
    Receipt ((13:Fin 16),(16:Fin 36),ti):=by decide
theorem receipt_13_y17:∀ ti:Fin 51,
    Receipt ((13:Fin 16),(17:Fin 36),ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
