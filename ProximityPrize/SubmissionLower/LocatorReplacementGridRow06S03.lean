import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y06_t00_01_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_06_y06_t00_01 : RowTileReceipt 6 6 7 0 1 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 0 1 receipt_row_06_y06_t00_01_fixed

private theorem receipt_row_06_y06_t01_09_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 1 9 := by decide +kernel

theorem receipt_row_06_y06_t01_09 : RowTileReceipt 6 6 7 1 9 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 1 9 receipt_row_06_y06_t01_09_fixed

private theorem receipt_row_06_y06_t09_26_fixed :
    FixedYReceipt 6 ⟨6, by decide⟩ 9 26 := by decide +kernel

theorem receipt_row_06_y06_t09_26 : RowTileReceipt 6 6 7 9 26 :=
  fixedYReceipt_to_rowTile 6 ⟨6, by decide⟩ 9 26 receipt_row_06_y06_t09_26_fixed

private theorem receipt_row_06_y07_t00_02_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_06_y07_t00_02 : RowTileReceipt 6 7 8 0 2 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 0 2 receipt_row_06_y07_t00_02_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
