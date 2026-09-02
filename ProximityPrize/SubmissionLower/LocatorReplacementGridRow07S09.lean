import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_y07_t15_17_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 15 17 := by decide +kernel

theorem receipt_row_07_y07_t15_17 : RowTileReceipt 7 7 8 15 17 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 15 17 receipt_row_07_y07_t15_17_fixed

private theorem receipt_row_07_y07_t17_19_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 17 19 := by decide +kernel

theorem receipt_row_07_y07_t17_19 : RowTileReceipt 7 7 8 17 19 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 17 19 receipt_row_07_y07_t17_19_fixed

private theorem receipt_row_07_y07_t19_21_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 19 21 := by decide +kernel

theorem receipt_row_07_y07_t19_21 : RowTileReceipt 7 7 8 19 21 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 19 21 receipt_row_07_y07_t19_21_fixed


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
