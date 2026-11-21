import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Low51At2403AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total0 : ((rows 0).map (price 0)).sum = 95 := by decide +kernel

theorem row_total1 : ((rows 1).map (price 1)).sum = 376 := by decide +kernel

theorem row_total2 : ((rows 2).map (price 2)).sum = 930 := by decide +kernel

theorem row_total3 : ((rows 3).map (price 3)).sum = 1840 := by decide +kernel

theorem row_total4 : ((rows 4).map (price 4)).sum = 3185 := by decide +kernel

theorem row_total5 : ((rows 5).map (price 5)).sum = 5040 := by decide +kernel

theorem row_total6 : ((rows 6).map (price 6)).sum = 7476 := by decide +kernel

theorem row_total7 : ((rows 7).map (price 7)).sum = 10560 := by decide +kernel

theorem row_total8 : ((rows 8).map (price 8)).sum = 14355 := by decide +kernel

theorem row_total9 : ((rows 9).map (price 9)).sum = 18920 := by decide +kernel

theorem row_total10 : ((rows 10).map (price 10)).sum = 24310 := by decide +kernel

theorem row_total11 : ((rows 11).map (price 11)).sum = 30576 := by decide +kernel

theorem row_total12 : ((rows 12).map (price 12)).sum = 37765 := by decide +kernel

theorem row_total13 : ((rows 13).map (price 13)).sum = 45920 := by decide +kernel

theorem row_total14 : ((rows 14).map (price 14)).sum = 54999 := by decide +kernel

theorem row_total15 : ((rows 15).map (price 15)).sum = 64960 := by decide +kernel

theorem row_total16 : ((rows 16).map (price 16)).sum = 75761 := by decide +kernel

theorem row_total17 : ((rows 17).map (price 17)).sum = 87360 := by decide +kernel

theorem row_total18 : ((rows 18).map (price 18)).sum = 99715 := by decide +kernel

theorem row_total19 : ((rows 19).map (price 19)).sum = 112784 := by decide +kernel

end Low51At2403AnchorRankReceipt
