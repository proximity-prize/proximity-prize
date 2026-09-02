import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y07_t09_11_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 9 11 := by decide +kernel

theorem receipt_row_07_y07_t09_11 : RowTileReceipt 7 7 8 9 11 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 9 11 receipt_row_07_y07_t09_11_fixed

private theorem receipt_row_07_y07_t11_13_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 11 13 := by decide +kernel

theorem receipt_row_07_y07_t11_13 : RowTileReceipt 7 7 8 11 13 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 11 13 receipt_row_07_y07_t11_13_fixed

private theorem receipt_row_07_y07_t13_15_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 13 15 := by decide +kernel

theorem receipt_row_07_y07_t13_15 : RowTileReceipt 7 7 8 13 15 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 13 15 receipt_row_07_y07_t13_15_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
