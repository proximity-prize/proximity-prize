import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y00_t00_24_fixed :
    FixedYReceipt 7 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_07_y00_t00_24 : RowTileReceipt 7 0 1 0 24 :=
  fixedYReceipt_to_rowTile 7 ⟨0, by decide⟩ 0 24 receipt_row_07_y00_t00_24_fixed

private theorem receipt_row_07_y00_t24_26_fixed :
    FixedYReceipt 7 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_07_y00_t24_26 : RowTileReceipt 7 0 1 24 26 :=
  fixedYReceipt_to_rowTile 7 ⟨0, by decide⟩ 24 26 receipt_row_07_y00_t24_26_fixed

private theorem receipt_row_07_y01_t00_24_fixed :
    FixedYReceipt 7 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_07_y01_t00_24 : RowTileReceipt 7 1 2 0 24 :=
  fixedYReceipt_to_rowTile 7 ⟨1, by decide⟩ 0 24 receipt_row_07_y01_t00_24_fixed

private theorem receipt_row_07_y01_t24_26_fixed :
    FixedYReceipt 7 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_07_y01_t24_26 : RowTileReceipt 7 1 2 24 26 :=
  fixedYReceipt_to_rowTile 7 ⟨1, by decide⟩ 24 26 receipt_row_07_y01_t24_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
