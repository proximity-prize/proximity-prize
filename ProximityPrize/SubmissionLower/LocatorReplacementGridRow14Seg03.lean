import ProximityPrize.SubmissionLower.LocatorReplacementGridRow14Seg02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_14_y_06_fixed :
    FixedYReceipt 14 ⟨6, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_14_y_06 : RowBandReceipt 14 6 7 :=
  fixedYReceipt_to_rowBand 14 ⟨6, by decide⟩ receipt_row_14_y_06_fixed

private theorem receipt_row_14_y_07_fixed :
    FixedYReceipt 14 ⟨7, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_14_y_07 : RowBandReceipt 14 7 8 :=
  fixedYReceipt_to_rowBand 14 ⟨7, by decide⟩ receipt_row_14_y_07_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
