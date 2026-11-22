import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt50 -- serialize candidate build

set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total53 : ((rows 53).map (price 53)).sum = 5578281 := by decide +kernel

end Cutter53AnchorRankReceipt
