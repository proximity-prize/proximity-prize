import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt

theorem row_total53 : ((rows 53).map (price 53)).sum = 5578281 := by
  change ((rowsFrom chunks53).map (price 53)).sum = _
  rw [chunkFees_eq]
  decide +kernel

end Cutter53AnchorRankReceipt
