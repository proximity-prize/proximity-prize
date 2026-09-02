import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y07_t02_04_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_06_y07_t02_04 : RowTileReceipt 6 7 8 2 4 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 2 4 receipt_row_06_y07_t02_04_fixed

private theorem receipt_row_06_y07_t04_12_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 4 12 := by decide +kernel

theorem receipt_row_06_y07_t04_12 : RowTileReceipt 6 7 8 4 12 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 4 12 receipt_row_06_y07_t04_12_fixed

private theorem receipt_row_06_y07_t12_26_fixed :
    FixedYReceipt 6 ⟨7, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_06_y07_t12_26 : RowTileReceipt 6 7 8 12 26 :=
  fixedYReceipt_to_rowTile 6 ⟨7, by decide⟩ 12 26 receipt_row_06_y07_t12_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
