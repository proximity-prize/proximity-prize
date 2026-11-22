import ProximityPrize.SubmissionLower.Low51EdgeRankReceipt
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt

theorem row_total20 : ((rows 20).map (price 20)).sum = 128212 := by
  change ((rowsFrom chunks20).map (price 20)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total21 : ((rows 21).map (price 21)).sum = 142575 := by
  change ((rowsFrom chunks21).map (price 21)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total22 : ((rows 22).map (price 22)).sum = 157028 := by
  change ((rowsFrom chunks22).map (price 22)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total23 : ((rows 23).map (price 23)).sum = 171258 := by
  change ((rowsFrom chunks23).map (price 23)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total24 : ((rows 24).map (price 24)).sum = 184968 := by
  change ((rowsFrom chunks24).map (price 24)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total25 : ((rows 25).map (price 25)).sum = 197877 := by
  change ((rowsFrom chunks25).map (price 25)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total26 : ((rows 26).map (price 26)).sum = 209720 := by
  change ((rowsFrom chunks26).map (price 26)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total27 : ((rows 27).map (price 27)).sum = 220248 := by
  change ((rowsFrom chunks27).map (price 27)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total28 : ((rows 28).map (price 28)).sum = 229432 := by
  change ((rowsFrom chunks28).map (price 28)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total29 : ((rows 29).map (price 29)).sum = 237381 := by
  change ((rowsFrom chunks29).map (price 29)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total30 : ((rows 30).map (price 30)).sum = 244134 := by
  change ((rowsFrom chunks30).map (price 30)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total31 : ((rows 31).map (price 31)).sum = 249795 := by
  change ((rowsFrom chunks31).map (price 31)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total32 : ((rows 32).map (price 32)).sum = 254400 := by
  change ((rowsFrom chunks32).map (price 32)).sum = _
  rw [chunkFees_eq]
  decide +kernel

theorem row_total33 : ((rows 33).map (price 33)).sum = 258048 := by
  change ((rowsFrom chunks33).map (price 33)).sum = _
  rw [chunkFees_eq]
  decide +kernel

end Cutter53AnchorRankReceipt
