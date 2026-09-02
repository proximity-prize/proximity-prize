import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_y06_t01_02_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 1 2 := by decide +kernel

theorem receipt_row_08_y06_t01_02 : RowTileReceipt 8 6 7 1 2 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 1 2 receipt_row_08_y06_t01_02_fixed

private theorem receipt_row_08_y06_t02_04_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 2 4 := by decide +kernel

theorem receipt_row_08_y06_t02_04 : RowTileReceipt 8 6 7 2 4 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 2 4 receipt_row_08_y06_t02_04_fixed

private theorem receipt_row_08_y06_t04_06_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 4 6 := by decide +kernel

theorem receipt_row_08_y06_t04_06 : RowTileReceipt 8 6 7 4 6 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 4 6 receipt_row_08_y06_t04_06_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
