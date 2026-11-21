import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt (rows)

theorem row_total0 : ((rows 0).map (price 0)).sum = 96 := by decide +kernel

theorem row_total1 : ((rows 1).map (price 1)).sum = 380 := by decide +kernel

theorem row_total2 : ((rows 2).map (price 2)).sum = 940 := by decide +kernel

theorem row_total3 : ((rows 3).map (price 3)).sum = 1860 := by decide +kernel

theorem row_total4 : ((rows 4).map (price 4)).sum = 3220 := by decide +kernel

theorem row_total5 : ((rows 5).map (price 5)).sum = 5096 := by decide +kernel

theorem row_total6 : ((rows 6).map (price 6)).sum = 7560 := by decide +kernel

theorem row_total7 : ((rows 7).map (price 7)).sum = 10680 := by decide +kernel

theorem row_total8 : ((rows 8).map (price 8)).sum = 14520 := by decide +kernel

theorem row_total9 : ((rows 9).map (price 9)).sum = 19140 := by decide +kernel

theorem row_total10 : ((rows 10).map (price 10)).sum = 24596 := by decide +kernel

theorem row_total11 : ((rows 11).map (price 11)).sum = 30940 := by decide +kernel

theorem row_total12 : ((rows 12).map (price 12)).sum = 38220 := by decide +kernel

theorem row_total13 : ((rows 13).map (price 13)).sum = 46480 := by decide +kernel

theorem row_total14 : ((rows 14).map (price 14)).sum = 55678 := by decide +kernel

theorem row_total15 : ((rows 15).map (price 15)).sum = 65772 := by decide +kernel

theorem row_total16 : ((rows 16).map (price 16)).sum = 76720 := by decide +kernel

theorem row_total17 : ((rows 17).map (price 17)).sum = 88480 := by decide +kernel

theorem row_total18 : ((rows 18).map (price 18)).sum = 101010 := by decide +kernel

theorem row_total19 : ((rows 19).map (price 19)).sum = 114268 := by decide +kernel

end Cutter53AnchorRankReceipt
