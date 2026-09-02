import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10Seg04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_10_y_10_fixed :
    FixedYReceipt 10 ⟨10, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_10_y_10 : RowBandReceipt 10 10 11 :=
  fixedYReceipt_to_rowBand 10 ⟨10, by decide⟩ receipt_row_10_y_10_fixed

private theorem receipt_row_10_y_11_fixed :
    FixedYReceipt 10 ⟨11, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_10_y_11 : RowBandReceipt 10 11 12 :=
  fixedYReceipt_to_rowBand 10 ⟨11, by decide⟩ receipt_row_10_y_11_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
