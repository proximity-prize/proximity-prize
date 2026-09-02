import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_y08_t11_13_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 11 13 := by decide +kernel

theorem receipt_row_06_y08_t11_13 : RowTileReceipt 6 8 9 11 13 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 11 13 receipt_row_06_y08_t11_13_fixed

private theorem receipt_row_06_y08_t13_21_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 13 21 := by decide +kernel

theorem receipt_row_06_y08_t13_21 : RowTileReceipt 6 8 9 13 21 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 13 21 receipt_row_06_y08_t13_21_fixed

private theorem receipt_row_06_y08_t21_26_fixed :
    FixedYReceipt 6 ⟨8, by decide⟩ 21 26 := by decide +kernel

theorem receipt_row_06_y08_t21_26 : RowTileReceipt 6 8 9 21 26 :=
  fixedYReceipt_to_rowTile 6 ⟨8, by decide⟩ 21 26 receipt_row_06_y08_t21_26_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
