import ProximityPrize.SubmissionLower.LocatorReplacementGridRow11Seg04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_y_10_fixed :
    FixedYReceipt 11 ⟨10, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y_10 : RowBandReceipt 11 10 11 :=
  fixedYReceipt_to_rowBand 11 ⟨10, by decide⟩ receipt_row_11_y_10_fixed

private theorem receipt_row_11_y_11_fixed :
    FixedYReceipt 11 ⟨11, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y_11 : RowBandReceipt 11 11 12 :=
  fixedYReceipt_to_rowBand 11 ⟨11, by decide⟩ receipt_row_11_y_11_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
