import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total50 : ((rows 50).map (price 50)).sum = 226101 := by decide +kernel

theorem row_total51 : ((rows 51).map (price 51)).sum = 252195 := by decide +kernel

theorem row_total52 : ((rows 52).map (price 52)).sum = 216598 := by decide +kernel

end Cutter53AnchorRankReceipt
