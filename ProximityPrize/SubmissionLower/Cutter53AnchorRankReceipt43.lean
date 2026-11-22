import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt

theorem row_total43 : ((rows 43).map (price 43)).sum = 266355 := by
  change ((rowsFrom chunks43).map (price 43)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total44 : ((rows 44).map (price 44)).sum = 250953 := by
  change ((rowsFrom chunks44).map (price 44)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total45 : ((rows 45).map (price 45)).sum = 263612 := by
  change ((rowsFrom chunks45).map (price 45)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total46 : ((rows 46).map (price 46)).sum = 243557 := by
  change ((rowsFrom chunks46).map (price 46)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total47 : ((rows 47).map (price 47)).sum = 260141 := by
  change ((rowsFrom chunks47).map (price 47)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total48 : ((rows 48).map (price 48)).sum = 235175 := by
  change ((rowsFrom chunks48).map (price 48)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total49 : ((rows 49).map (price 49)).sum = 256238 := by
  change ((rowsFrom chunks49).map (price 49)).sum = _
  rw [chunkFees_eq]
  decide +kernel

end Cutter53AnchorRankReceipt
