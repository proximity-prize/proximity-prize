import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y08_t05_07_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_06_y08_t05_07 : RowTileReceipt 6 8 9 5 7 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 5 7 receipt_row_06_y08_t05_07_fixed

private theorem receipt_row_06_y08_t07_09_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 7 9 := by decide +kernel

theorem receipt_row_06_y08_t07_09 : RowTileReceipt 6 8 9 7 9 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 7 9 receipt_row_06_y08_t07_09_fixed

private theorem receipt_row_06_y08_t09_11_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 9 11 := by decide +kernel

theorem receipt_row_06_y08_t09_11 : RowTileReceipt 6 8 9 9 11 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 9 11 receipt_row_06_y08_t09_11_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
