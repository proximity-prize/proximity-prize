import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y04_t00_08_fixed :
    FixedYReceipt 6 ⟨4, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_06_y04_t00_08 : RowTileReceipt 6 4 5 0 8 :=
  fixedYReceipt_to_rowTile 6 ⟨4, by decide⟩ 0 8 receipt_row_06_y04_t00_08_fixed

private theorem receipt_row_06_y04_t08_26_fixed :
    FixedYReceipt 6 ⟨4, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_06_y04_t08_26 : RowTileReceipt 6 4 5 8 26 :=
  fixedYReceipt_to_rowTile 6 ⟨4, by decide⟩ 8 26 receipt_row_06_y04_t08_26_fixed

private theorem receipt_row_06_y05_t00_08_fixed :
    FixedYReceipt 6 ⟨5, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_06_y05_t00_08 : RowTileReceipt 6 5 6 0 8 :=
  fixedYReceipt_to_rowTile 6 ⟨5, by decide⟩ 0 8 receipt_row_06_y05_t00_08_fixed

private theorem receipt_row_06_y05_t08_26_fixed :
    FixedYReceipt 6 ⟨5, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_06_y05_t08_26 : RowTileReceipt 6 5 6 8 26 :=
  fixedYReceipt_to_rowTile 6 ⟨5, by decide⟩ 8 26 receipt_row_06_y05_t08_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
