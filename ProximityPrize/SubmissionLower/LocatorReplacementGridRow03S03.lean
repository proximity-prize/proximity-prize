import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_y06_t00_24_fixed :
    FixedYReceipt 3 ⟨6, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y06_t00_24 : RowTileReceipt 3 6 7 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨6, by decide⟩ 0 24 receipt_row_03_y06_t00_24_fixed

private theorem receipt_row_03_y06_t24_26_fixed :
    FixedYReceipt 3 ⟨6, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y06_t24_26 : RowTileReceipt 3 6 7 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨6, by decide⟩ 24 26 receipt_row_03_y06_t24_26_fixed

private theorem receipt_row_03_y07_t00_26_fixed :
    FixedYReceipt 3 ⟨7, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_03_y07_t00_26 : RowTileReceipt 3 7 8 0 26 :=
  fixedYReceipt_to_rowTile 3 ⟨7, by decide⟩ 0 26 receipt_row_03_y07_t00_26_fixed

private theorem receipt_row_03_y08_t00_26_fixed :
    FixedYReceipt 3 ⟨8, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_03_y08_t00_26 : RowTileReceipt 3 8 9 0 26 :=
  fixedYReceipt_to_rowTile 3 ⟨8, by decide⟩ 0 26 receipt_row_03_y08_t00_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
