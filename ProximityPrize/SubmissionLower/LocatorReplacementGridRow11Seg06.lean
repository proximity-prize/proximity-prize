import ProximityPrize.SubmissionLower.LocatorReplacementGridRow11Seg05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_y_12_fixed :
    FixedYReceipt 11 ⟨12, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_11_y_12 : RowBandReceipt 11 12 13 :=
  fixedYReceipt_to_rowBand 11 ⟨12, by decide⟩ receipt_row_11_y_12_fixed

private theorem receipt_row_11_y_13_fixed :
    FixedYReceipt 11 ⟨13, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_11_y_13 : RowBandReceipt 11 13 14 :=
  fixedYReceipt_to_rowBand 11 ⟨13, by decide⟩ receipt_row_11_y_13_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
