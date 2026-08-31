import ProximityPrize.SubmissionLower.LocatorReplacementReceipt10Chunk4
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_10_y30:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(30:Fin 36),ti):=by decide
theorem receipt_10_y31:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(31:Fin 36),ti):=by decide
theorem receipt_10_y32:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(32:Fin 36),ti):=by decide
theorem receipt_10_y33:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(33:Fin 36),ti):=by decide
theorem receipt_10_y34:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(34:Fin 36),ti):=by decide
theorem receipt_10_y35:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(35:Fin 36),ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
