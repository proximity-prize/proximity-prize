import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y06_t07_26_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 7 26 := by decide +kernel

theorem receipt_row_07_y06_t07_26 : RowTileReceipt 7 6 7 7 26 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 7 26 receipt_row_07_y06_t07_26_fixed

private theorem receipt_row_07_y07_t00_01_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_07_y07_t00_01 : RowTileReceipt 7 7 8 0 1 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 0 1 receipt_row_07_y07_t00_01_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
