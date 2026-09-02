import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y06_t01_03_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_07_y06_t01_03 : RowTileReceipt 7 6 7 1 3 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 1 3 receipt_row_07_y06_t01_03_fixed

private theorem receipt_row_07_y06_t03_05_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_07_y06_t03_05 : RowTileReceipt 7 6 7 3 5 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 3 5 receipt_row_07_y06_t03_05_fixed

private theorem receipt_row_07_y06_t05_07_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_07_y06_t05_07 : RowTileReceipt 7 6 7 5 7 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 5 7 receipt_row_07_y06_t05_07_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
