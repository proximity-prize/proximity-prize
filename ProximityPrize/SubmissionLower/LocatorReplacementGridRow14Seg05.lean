import ProximityPrize.SubmissionLower.LocatorReplacementGridRow14Seg04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_14_y_10_fixed :
    FixedYReceipt 14 ⟨10, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_14_y_10 : RowBandReceipt 14 10 11 :=
  fixedYReceipt_to_rowBand 14 ⟨10, by decide⟩ receipt_row_14_y_10_fixed

private theorem receipt_row_14_y_11_fixed :
    FixedYReceipt 14 ⟨11, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_14_y_11 : RowBandReceipt 14 11 12 :=
  fixedYReceipt_to_rowBand 14 ⟨11, by decide⟩ receipt_row_14_y_11_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
