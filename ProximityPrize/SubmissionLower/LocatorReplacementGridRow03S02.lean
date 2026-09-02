import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_y04_t00_24_fixed :
    FixedYReceipt 3 ⟨4, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y04_t00_24 : RowTileReceipt 3 4 5 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨4, by decide⟩ 0 24 receipt_row_03_y04_t00_24_fixed

private theorem receipt_row_03_y04_t24_26_fixed :
    FixedYReceipt 3 ⟨4, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y04_t24_26 : RowTileReceipt 3 4 5 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨4, by decide⟩ 24 26 receipt_row_03_y04_t24_26_fixed

private theorem receipt_row_03_y05_t00_24_fixed :
    FixedYReceipt 3 ⟨5, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_y05_t00_24 : RowTileReceipt 3 5 6 0 24 :=
  fixedYReceipt_to_rowTile 3 ⟨5, by decide⟩ 0 24 receipt_row_03_y05_t00_24_fixed

private theorem receipt_row_03_y05_t24_26_fixed :
    FixedYReceipt 3 ⟨5, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_03_y05_t24_26 : RowTileReceipt 3 5 6 24 26 :=
  fixedYReceipt_to_rowTile 3 ⟨5, by decide⟩ 24 26 receipt_row_03_y05_t24_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
