import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_y06_t00_10_fixed :
    FixedYReceipt 5 ⟨6, by decide⟩ 0 10 := by decide +kernel

theorem receipt_row_05_y06_t00_10 : RowTileReceipt 5 6 7 0 10 :=
  fixedYReceipt_to_rowTile 5 ⟨6, by decide⟩ 0 10 receipt_row_05_y06_t00_10_fixed

private theorem receipt_row_05_y06_t10_26_fixed :
    FixedYReceipt 5 ⟨6, by decide⟩ 10 26 := by decide +kernel

theorem receipt_row_05_y06_t10_26 : RowTileReceipt 5 6 7 10 26 :=
  fixedYReceipt_to_rowTile 5 ⟨6, by decide⟩ 10 26 receipt_row_05_y06_t10_26_fixed

private theorem receipt_row_05_y07_t00_02_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y07_t00_02 : RowTileReceipt 5 7 8 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 0 2 receipt_row_05_y07_t00_02_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
