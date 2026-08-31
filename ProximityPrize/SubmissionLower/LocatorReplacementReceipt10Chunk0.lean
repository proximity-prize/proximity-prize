import ProximityPrize.SubmissionLower.LocatorReplacementReceipt9
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_10_y0:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(0:Fin 36),ti):=by decide
theorem receipt_10_y1:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(1:Fin 36),ti):=by decide
theorem receipt_10_y2:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(2:Fin 36),ti):=by decide
theorem receipt_10_y3:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(3:Fin 36),ti):=by decide
theorem receipt_10_y4:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(4:Fin 36),ti):=by decide
theorem receipt_10_y5:∀ ti:Fin 51,
    Receipt ((10:Fin 16),(5:Fin 36),ti):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
