import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y07_t21_23_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 21 23 := by decide +kernel

theorem receipt_row_07_y07_t21_23 : RowTileReceipt 7 7 8 21 23 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 21 23 receipt_row_07_y07_t21_23_fixed

private theorem receipt_row_07_y07_t23_25_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 23 25 := by decide +kernel

theorem receipt_row_07_y07_t23_25 : RowTileReceipt 7 7 8 23 25 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 23 25 receipt_row_07_y07_t23_25_fixed

private theorem receipt_row_07_y07_t25_26_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 25 26 := by decide +kernel

theorem receipt_row_07_y07_t25_26 : RowTileReceipt 7 7 8 25 26 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 25 26 receipt_row_07_y07_t25_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
