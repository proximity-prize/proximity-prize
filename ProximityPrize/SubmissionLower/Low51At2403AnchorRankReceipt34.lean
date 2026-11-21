import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Low51At2403AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total34 : ((rows 34).map (price 34)).sum = 257339 := by decide +kernel

theorem row_total35 : ((rows 35).map (price 35)).sum = 259623 := by decide +kernel

theorem row_total36 : ((rows 36).map (price 36)).sum = 261211 := by decide +kernel

theorem row_total37 : ((rows 37).map (price 37)).sum = 262196 := by decide +kernel

theorem row_total38 : ((rows 38).map (price 38)).sum = 262586 := by decide +kernel

theorem row_total39 : ((rows 39).map (price 39)).sum = 262469 := by decide +kernel

theorem row_total40 : ((rows 40).map (price 40)).sum = 261853 := by decide +kernel

theorem row_total41 : ((rows 41).map (price 41)).sum = 260820 := by decide +kernel

theorem row_total42 : ((rows 42).map (price 42)).sum = 259377 := by decide +kernel

end Low51At2403AnchorRankReceipt
