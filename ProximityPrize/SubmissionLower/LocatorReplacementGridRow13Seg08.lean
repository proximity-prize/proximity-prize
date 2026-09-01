import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y_16_fixed :
    FixedYReceipt 13 ⟨16, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_13_y_16 : RowBandReceipt 13 16 17 :=
  fixedYReceipt_to_rowBand 13 ⟨16, by decide⟩ receipt_row_13_y_16_fixed

private theorem receipt_row_13_y_17_fixed :
    FixedYReceipt 13 ⟨17, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_13_y_17 : RowBandReceipt 13 17 18 :=
  fixedYReceipt_to_rowBand 13 ⟨17, by decide⟩ receipt_row_13_y_17_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
