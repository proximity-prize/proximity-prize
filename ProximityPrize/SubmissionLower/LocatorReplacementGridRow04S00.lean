import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_y00_t00_24_fixed :
    FixedYReceipt 4 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_y00_t00_24 : RowTileReceipt 4 0 1 0 24 :=
  fixedYReceipt_to_rowTile 4 ⟨0, by decide⟩ 0 24 receipt_row_04_y00_t00_24_fixed

private theorem receipt_row_04_y00_t24_26_fixed :
    FixedYReceipt 4 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_04_y00_t24_26 : RowTileReceipt 4 0 1 24 26 :=
  fixedYReceipt_to_rowTile 4 ⟨0, by decide⟩ 24 26 receipt_row_04_y00_t24_26_fixed

private theorem receipt_row_04_y01_t00_24_fixed :
    FixedYReceipt 4 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_04_y01_t00_24 : RowTileReceipt 4 1 2 0 24 :=
  fixedYReceipt_to_rowTile 4 ⟨1, by decide⟩ 0 24 receipt_row_04_y01_t00_24_fixed

private theorem receipt_row_04_y01_t24_26_fixed :
    FixedYReceipt 4 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_04_y01_t24_26 : RowTileReceipt 4 1 2 24 26 :=
  fixedYReceipt_to_rowTile 4 ⟨1, by decide⟩ 24 26 receipt_row_04_y01_t24_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
