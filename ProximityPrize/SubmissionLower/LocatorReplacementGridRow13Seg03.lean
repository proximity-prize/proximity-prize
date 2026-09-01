import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y_06_fixed :
    FixedYReceipt 13 ⟨6, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_13_y_06 : RowBandReceipt 13 6 7 :=
  fixedYReceipt_to_rowBand 13 ⟨6, by decide⟩ receipt_row_13_y_06_fixed

private theorem receipt_row_13_y_07_fixed :
    FixedYReceipt 13 ⟨7, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_13_y_07 : RowBandReceipt 13 7 8 :=
  fixedYReceipt_to_rowBand 13 ⟨7, by decide⟩ receipt_row_13_y_07_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
