import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt34 -- serialize candidate build

set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total43 : ((rows 43).map (price 43)).sum = 266355 := by decide +kernel

theorem row_total44 : ((rows 44).map (price 44)).sum = 250953 := by decide +kernel

theorem row_total45 : ((rows 45).map (price 45)).sum = 263612 := by decide +kernel

theorem row_total46 : ((rows 46).map (price 46)).sum = 243557 := by decide +kernel

theorem row_total47 : ((rows 47).map (price 47)).sum = 260141 := by decide +kernel

theorem row_total48 : ((rows 48).map (price 48)).sum = 235175 := by decide +kernel

theorem row_total49 : ((rows 49).map (price 49)).sum = 256238 := by decide +kernel

end Cutter53AnchorRankReceipt
