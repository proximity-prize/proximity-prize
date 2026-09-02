import ProximityPrize.SubmissionLower.LocatorReplacementGridRow18Seg09

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_18_y_20_fixed :
    FixedYReceipt 18 ⟨20, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_18_y_20 : RowBandReceipt 18 20 21 :=
  fixedYReceipt_to_rowBand 18 ⟨20, by decide⟩ receipt_row_18_y_20_fixed

private theorem receipt_row_18_y_21_fixed :
    FixedYReceipt 18 ⟨21, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_18_y_21 : RowBandReceipt 18 21 22 :=
  fixedYReceipt_to_rowBand 18 ⟨21, by decide⟩ receipt_row_18_y_21_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
