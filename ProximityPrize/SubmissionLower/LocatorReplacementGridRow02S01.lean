import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_02_y02_t00_24_fixed :
    FixedYReceipt 2 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y02_t00_24 : RowTileReceipt 2 2 3 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨2, by decide⟩ 0 24 receipt_row_02_y02_t00_24_fixed

private theorem receipt_row_02_y02_t24_26_fixed :
    FixedYReceipt 2 ⟨2, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y02_t24_26 : RowTileReceipt 2 2 3 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨2, by decide⟩ 24 26 receipt_row_02_y02_t24_26_fixed

private theorem receipt_row_02_y03_t00_24_fixed :
    FixedYReceipt 2 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_02_y03_t00_24 : RowTileReceipt 2 3 4 0 24 :=
  fixedYReceipt_to_rowTile 2 ⟨3, by decide⟩ 0 24 receipt_row_02_y03_t00_24_fixed

private theorem receipt_row_02_y03_t24_26_fixed :
    FixedYReceipt 2 ⟨3, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_02_y03_t24_26 : RowTileReceipt 2 3 4 24 26 :=
  fixedYReceipt_to_rowTile 2 ⟨3, by decide⟩ 24 26 receipt_row_02_y03_t24_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
