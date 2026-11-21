import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Low51At2403AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total53 : ((rows 53).map (price 53)).sum = 5309396 := by decide +kernel

end Low51At2403AnchorRankReceipt
