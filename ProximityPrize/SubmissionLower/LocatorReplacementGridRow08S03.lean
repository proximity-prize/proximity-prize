import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_y05_t00_01_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 0 1 := by decide +kernel

theorem receipt_row_08_y05_t00_01 : RowTileReceipt 8 5 6 0 1 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 0 1 receipt_row_08_y05_t00_01_fixed

private theorem receipt_row_08_y05_t01_03_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 1 3 := by decide +kernel

theorem receipt_row_08_y05_t01_03 : RowTileReceipt 8 5 6 1 3 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 1 3 receipt_row_08_y05_t01_03_fixed

private theorem receipt_row_08_y05_t03_05_fixed :
    FixedYReceipt 8 ⟨5, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_08_y05_t03_05 : RowTileReceipt 8 5 6 3 5 :=
  fixedYReceipt_to_rowTile 8 ⟨5, by decide⟩ 3 5 receipt_row_08_y05_t03_05_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
