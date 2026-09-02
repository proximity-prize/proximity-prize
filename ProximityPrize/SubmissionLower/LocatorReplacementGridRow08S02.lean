import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_y04_t00_01_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_08_y04_t00_01 : RowTileReceipt 8 4 5 0 1 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 0 1 receipt_row_08_y04_t00_01_fixed

private theorem receipt_row_08_y04_t01_09_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 1 9 := by decide +kernel

theorem receipt_row_08_y04_t01_09 : RowTileReceipt 8 4 5 1 9 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 1 9 receipt_row_08_y04_t01_09_fixed

private theorem receipt_row_08_y04_t09_26_fixed :
    FixedYReceipt 8 ⟨4, by decide⟩ 9 26 := by decide +kernel

theorem receipt_row_08_y04_t09_26 : RowTileReceipt 8 4 5 9 26 :=
  fixedYReceipt_to_rowTile 8 ⟨4, by decide⟩ 9 26 receipt_row_08_y04_t09_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
