import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y07_t03_05_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_07_y07_t03_05 : RowTileReceipt 7 7 8 3 5 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 3 5 receipt_row_07_y07_t03_05_fixed

private theorem receipt_row_07_y07_t05_07_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_07_y07_t05_07 : RowTileReceipt 7 7 8 5 7 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 5 7 receipt_row_07_y07_t05_07_fixed

private theorem receipt_row_07_y07_t07_09_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 7 9 := by decide +kernel

theorem receipt_row_07_y07_t07_09 : RowTileReceipt 7 7 8 7 9 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 7 9 receipt_row_07_y07_t07_09_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
