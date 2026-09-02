import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_y07_t02_26_fixed :
    FixedYReceipt 5 ⟨7, by decide⟩ 2 26 := by decide +kernel

theorem receipt_row_05_y07_t02_26 : RowTileReceipt 5 7 8 2 26 :=
  fixedYReceipt_to_rowTile 5 ⟨7, by decide⟩ 2 26 receipt_row_05_y07_t02_26_fixed

private theorem receipt_row_05_y08_t00_02_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y08_t00_02 : RowTileReceipt 5 8 9 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 0 2 receipt_row_05_y08_t00_02_fixed

private theorem receipt_row_05_y08_t02_10_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 2 10 := by decide +kernel

theorem receipt_row_05_y08_t02_10 : RowTileReceipt 5 8 9 2 10 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 2 10 receipt_row_05_y08_t02_10_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
