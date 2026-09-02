import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_y05_t05_07_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_08_y05_t05_07 : RowTileReceipt 8 5 6 5 7 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 5 7 receipt_row_08_y05_t05_07_fixed

private theorem receipt_row_08_y05_t07_26_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 7 26 := by decide +kernel

theorem receipt_row_08_y05_t07_26 : RowTileReceipt 8 5 6 7 26 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 7 26 receipt_row_08_y05_t07_26_fixed

private theorem receipt_row_08_y06_t00_01_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_08_y06_t00_01 : RowTileReceipt 8 6 7 0 1 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 0 1 receipt_row_08_y06_t00_01_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
