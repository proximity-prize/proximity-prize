import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_y06_t00_25_fixed :
    FixedYReceipt 4 ⟨6, by decide⟩ 0 25 := by decide +kernel

theorem receipt_row_04_y06_t00_25 : RowTileReceipt 4 6 7 0 25 :=
  fixedYReceipt_to_rowTile 4 ⟨6, by decide⟩ 0 25 receipt_row_04_y06_t00_25_fixed

private theorem receipt_row_04_y06_t25_26_fixed :
    FixedYReceipt 4 ⟨6, by decide⟩ 25 26 := by decide +kernel

theorem receipt_row_04_y06_t25_26 : RowTileReceipt 4 6 7 25 26 :=
  fixedYReceipt_to_rowTile 4 ⟨6, by decide⟩ 25 26 receipt_row_04_y06_t25_26_fixed

private theorem receipt_row_04_y07_t00_12_fixed :
    FixedYReceipt 4 ⟨7, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_04_y07_t00_12 : RowTileReceipt 4 7 8 0 12 :=
  fixedYReceipt_to_rowTile 4 ⟨7, by decide⟩ 0 12 receipt_row_04_y07_t00_12_fixed

private theorem receipt_row_04_y07_t12_26_fixed :
    FixedYReceipt 4 ⟨7, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_04_y07_t12_26 : RowTileReceipt 4 7 8 12 26 :=
  fixedYReceipt_to_rowTile 4 ⟨7, by decide⟩ 12 26 receipt_row_04_y07_t12_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
