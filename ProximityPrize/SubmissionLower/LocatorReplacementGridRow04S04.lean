import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_y08_t00_12_fixed :
    FixedYReceipt 4 ⟨8, by decide⟩ 0 12 := by decide +kernel

theorem receipt_row_04_y08_t00_12 : RowTileReceipt 4 8 9 0 12 :=
  fixedYReceipt_to_rowTile 4 ⟨8, by decide⟩ 0 12 receipt_row_04_y08_t00_12_fixed

private theorem receipt_row_04_y08_t12_26_fixed :
    FixedYReceipt 4 ⟨8, by decide⟩ 12 26 := by decide +kernel

theorem receipt_row_04_y08_t12_26 : RowTileReceipt 4 8 9 12 26 :=
  fixedYReceipt_to_rowTile 4 ⟨8, by decide⟩ 12 26 receipt_row_04_y08_t12_26_fixed

private theorem receipt_row_04_y09_t00_02_fixed :
    FixedYReceipt 4 ⟨9, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_04_y09_t00_02 : RowTileReceipt 4 9 10 0 2 :=
  fixedYReceipt_to_rowTile 4 ⟨9, by decide⟩ 0 2 receipt_row_04_y09_t00_02_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
