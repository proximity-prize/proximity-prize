import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y04_t00_08_fixed :
    FixedYReceipt 7 ⟨4, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_07_y04_t00_08 : RowTileReceipt 7 4 5 0 8 :=
  fixedYReceipt_to_rowTile 7 ⟨4, by decide⟩ 0 8 receipt_row_07_y04_t00_08_fixed

private theorem receipt_row_07_y04_t08_26_fixed :
    FixedYReceipt 7 ⟨4, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_07_y04_t08_26 : RowTileReceipt 7 4 5 8 26 :=
  fixedYReceipt_to_rowTile 7 ⟨4, by decide⟩ 8 26 receipt_row_07_y04_t08_26_fixed

private theorem receipt_row_07_y05_t00_01_fixed :
    FixedYReceipt 7 ⟨5, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_07_y05_t00_01 : RowTileReceipt 7 5 6 0 1 :=
  fixedYReceipt_to_rowTile 7 ⟨5, by decide⟩ 0 1 receipt_row_07_y05_t00_01_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
