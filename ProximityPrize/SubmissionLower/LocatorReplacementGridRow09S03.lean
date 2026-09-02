import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_y04_t01_03_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_09_y04_t01_03 : RowTileReceipt 9 4 5 1 3 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 1 3 receipt_row_09_y04_t01_03_fixed

private theorem receipt_row_09_y04_t03_05_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_09_y04_t03_05 : RowTileReceipt 9 4 5 3 5 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 3 5 receipt_row_09_y04_t03_05_fixed

private theorem receipt_row_09_y04_t05_26_fixed :
    FixedYReceipt 9 ⟨4, by decide⟩ 5 26 := by decide +kernel

theorem receipt_row_09_y04_t05_26 : RowTileReceipt 9 4 5 5 26 :=
  fixedYReceipt_to_rowTile 9 ⟨4, by decide⟩ 5 26 receipt_row_09_y04_t05_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
