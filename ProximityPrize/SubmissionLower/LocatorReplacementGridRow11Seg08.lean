import ProximityPrize.SubmissionLower.LocatorReplacementGridRow11Seg07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_y_16_fixed :
    FixedYReceipt 11 ⟨16, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y_16 : RowBandReceipt 11 16 17 :=
  fixedYReceipt_to_rowBand 11 ⟨16, by decide⟩ receipt_row_11_y_16_fixed

private theorem receipt_row_11_y_17_fixed :
    FixedYReceipt 11 ⟨17, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_11_y_17 : RowBandReceipt 11 17 18 :=
  fixedYReceipt_to_rowBand 11 ⟨17, by decide⟩ receipt_row_11_y_17_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
