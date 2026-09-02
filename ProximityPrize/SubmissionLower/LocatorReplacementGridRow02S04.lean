import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_02_y09_t00_26_fixed :
    FixedYReceipt 2 ⟨9, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y09_t00_26 : RowTileReceipt 2 9 10 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨9, by decide⟩ 0 26 receipt_row_02_y09_t00_26_fixed

private theorem receipt_row_02_y10_t00_26_fixed :
    FixedYReceipt 2 ⟨10, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y10_t00_26 : RowTileReceipt 2 10 11 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨10, by decide⟩ 0 26 receipt_row_02_y10_t00_26_fixed

private theorem receipt_row_02_y11_t00_26_fixed :
    FixedYReceipt 2 ⟨11, by decide⟩ 0 26 := by decide +kernel

theorem receipt_row_02_y11_t00_26 : RowTileReceipt 2 11 12 0 26 :=
  fixedYReceipt_to_rowTile 2 ⟨11, by decide⟩ 0 26 receipt_row_02_y11_t00_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
