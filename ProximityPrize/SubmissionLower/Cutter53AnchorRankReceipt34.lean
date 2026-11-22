import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt

theorem row_total34 : ((rows 34).map (price 34)).sum = 261642 := by
  change ((rowsFrom chunks34).map (price 34)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total35 : ((rows 35).map (price 35)).sum = 262666 := by
  change ((rowsFrom chunks35).map (price 35)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total36 : ((rows 36).map (price 36)).sum = 266356 := by
  change ((rowsFrom chunks36).map (price 36)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total37 : ((rows 37).map (price 37)).sum = 264143 := by
  change ((rowsFrom chunks37).map (price 37)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total38 : ((rows 38).map (price 38)).sum = 263842 := by
  change ((rowsFrom chunks38).map (price 38)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total39 : ((rows 39).map (price 39)).sum = 268441 := by
  change ((rowsFrom chunks39).map (price 39)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total40 : ((rows 40).map (price 40)).sum = 261464 := by
  change ((rowsFrom chunks40).map (price 40)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total41 : ((rows 41).map (price 41)).sum = 268069 := by
  change ((rowsFrom chunks41).map (price 41)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total42 : ((rows 42).map (price 42)).sum = 257040 := by
  change ((rowsFrom chunks42).map (price 42)).sum = _
  rw [chunkFees_eq]
  decide +kernel

end Cutter53AnchorRankReceipt
