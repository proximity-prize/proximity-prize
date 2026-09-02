import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_y09_t00_12_fixed :
    FixedYReceipt 3 ⟨9, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_03_y09_t00_12 : RowTileReceipt 3 9 10 0 12 :=
  fixedYReceipt_to_rowTile 3 ⟨9, by decide⟩ 0 12 receipt_row_03_y09_t00_12_fixed

private theorem receipt_row_03_y09_t12_26_fixed :
    FixedYReceipt 3 ⟨9, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_03_y09_t12_26 : RowTileReceipt 3 9 10 12 26 :=
  fixedYReceipt_to_rowTile 3 ⟨9, by decide⟩ 12 26 receipt_row_03_y09_t12_26_fixed

private theorem receipt_row_03_y10_t00_12_fixed :
    FixedYReceipt 3 ⟨10, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_03_y10_t00_12 : RowTileReceipt 3 10 11 0 12 :=
  fixedYReceipt_to_rowTile 3 ⟨10, by decide⟩ 0 12 receipt_row_03_y10_t00_12_fixed

private theorem receipt_row_03_y10_t12_26_fixed :
    FixedYReceipt 3 ⟨10, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_03_y10_t12_26 : RowTileReceipt 3 10 11 12 26 :=
  fixedYReceipt_to_rowTile 3 ⟨10, by decide⟩ 12 26 receipt_row_03_y10_t12_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
