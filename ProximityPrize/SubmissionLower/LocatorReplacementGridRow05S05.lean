import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_05_y08_t10_26_fixed :
    FixedYReceipt 5 ⟨8, by decide⟩ 10 26 := by decide +kernel

theorem receipt_row_05_y08_t10_26 : RowTileReceipt 5 8 9 10 26 :=
  fixedYReceipt_to_rowTile 5 ⟨8, by decide⟩ 10 26 receipt_row_05_y08_t10_26_fixed

private theorem receipt_row_05_y09_t00_02_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 0 2 := by decide +kernel

theorem receipt_row_05_y09_t00_02 : RowTileReceipt 5 9 10 0 2 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 0 2 receipt_row_05_y09_t00_02_fixed

private theorem receipt_row_05_y09_t02_04_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_05_y09_t02_04 : RowTileReceipt 5 9 10 2 4 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 2 4 receipt_row_05_y09_t02_04_fixed

private theorem receipt_row_05_y09_t04_06_fixed :
    FixedYReceipt 5 ⟨9, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_05_y09_t04_06 : RowTileReceipt 5 9 10 4 6 :=
  fixedYReceipt_to_rowTile 5 ⟨9, by decide⟩ 4 6 receipt_row_05_y09_t04_06_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
