import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y07_t01_02_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_07_y07_t01_02 : RowTileReceipt 7 7 8 1 2 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 1 2 receipt_row_07_y07_t01_02_fixed

private theorem receipt_row_07_y07_t02_03_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 2 3 := by decide +kernel

theorem receipt_row_07_y07_t02_03 : RowTileReceipt 7 7 8 2 3 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 2 3 receipt_row_07_y07_t02_03_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
