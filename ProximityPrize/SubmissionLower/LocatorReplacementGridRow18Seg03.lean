import ProximityPrize.SubmissionLower.LocatorReplacementGridRow18Seg02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_18_y_06_fixed :
    FixedYReceipt 18 ⟨6, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_18_y_06 : RowBandReceipt 18 6 7 :=
  fixedYReceipt_to_rowBand 18 ⟨6, by decide⟩ receipt_row_18_y_06_fixed

private theorem receipt_row_18_y_07_fixed :
    FixedYReceipt 18 ⟨7, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_18_y_07 : RowBandReceipt 18 7 8 :=
  fixedYReceipt_to_rowBand 18 ⟨7, by decide⟩ receipt_row_18_y_07_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
