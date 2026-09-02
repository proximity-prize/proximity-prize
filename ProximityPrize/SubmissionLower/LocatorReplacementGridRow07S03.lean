import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y05_t01_03_fixed :
    FixedYReceipt 7 ⟨5, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_07_y05_t01_03 : RowTileReceipt 7 5 6 1 3 :=
  fixedYReceipt_to_rowTile 7 ⟨5, by decide⟩ 1 3 receipt_row_07_y05_t01_03_fixed

private theorem receipt_row_07_y05_t03_26_fixed :
    FixedYReceipt 7 ⟨5, by decide⟩ 3 26 := by decide +kernel

theorem receipt_row_07_y05_t03_26 : RowTileReceipt 7 5 6 3 26 :=
  fixedYReceipt_to_rowTile 7 ⟨5, by decide⟩ 3 26 receipt_row_07_y05_t03_26_fixed

private theorem receipt_row_07_y06_t00_01_fixed :
    FixedYReceipt 7 ⟨6, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_07_y06_t00_01 : RowTileReceipt 7 6 7 0 1 :=
  fixedYReceipt_to_rowTile 7 ⟨6, by decide⟩ 0 1 receipt_row_07_y06_t00_01_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
