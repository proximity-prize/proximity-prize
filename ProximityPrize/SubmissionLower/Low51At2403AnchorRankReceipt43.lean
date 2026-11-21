import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Low51At2403AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total43 : ((rows 43).map (price 43)).sum = 257603 := by decide +kernel

theorem row_total44 : ((rows 44).map (price 44)).sum = 255503 := by decide +kernel

theorem row_total45 : ((rows 45).map (price 45)).sum = 253153 := by decide +kernel

theorem row_total46 : ((rows 46).map (price 46)).sum = 250556 := by decide +kernel

theorem row_total47 : ((rows 47).map (price 47)).sum = 247787 := by decide +kernel

theorem row_total48 : ((rows 48).map (price 48)).sum = 244846 := by decide +kernel

theorem row_total49 : ((rows 49).map (price 49)).sum = 241806 := by decide +kernel

end Low51At2403AnchorRankReceipt
