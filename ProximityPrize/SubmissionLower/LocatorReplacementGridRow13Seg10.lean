import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg09

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y_20_fixed :
    FixedYReceipt 13 ⟨20, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y_20 : RowBandReceipt 13 20 21 :=
  fixedYReceipt_to_rowBand 13 ⟨20, by decide⟩ receipt_row_13_y_20_fixed

private theorem receipt_row_13_y_21_fixed :
    FixedYReceipt 13 ⟨21, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y_21 : RowBandReceipt 13 21 22 :=
  fixedYReceipt_to_rowBand 13 ⟨21, by decide⟩ receipt_row_13_y_21_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
