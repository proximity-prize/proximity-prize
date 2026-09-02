import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_02_y06_t00_24_fixed :
    FixedYReceipt 2 ⟨6, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y06_t00_24 : RowTileReceipt 2 6 7 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨6, by decide⟩ 0 24 receipt_row_02_y06_t00_24_fixed

private theorem receipt_row_02_y06_t24_26_fixed :
    FixedYReceipt 2 ⟨6, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y06_t24_26 : RowTileReceipt 2 6 7 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨6, by decide⟩ 24 26 receipt_row_02_y06_t24_26_fixed

private theorem receipt_row_02_y07_t00_26_fixed :
    FixedYReceipt 2 ⟨7, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y07_t00_26 : RowTileReceipt 2 7 8 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨7, by decide⟩ 0 26 receipt_row_02_y07_t00_26_fixed

private theorem receipt_row_02_y08_t00_26_fixed :
    FixedYReceipt 2 ⟨8, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y08_t00_26 : RowTileReceipt 2 8 9 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨8, by decide⟩ 0 26 receipt_row_02_y08_t00_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
