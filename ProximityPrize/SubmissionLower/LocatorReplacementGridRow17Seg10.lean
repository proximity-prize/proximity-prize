import ProximityPrize.SubmissionLower.LocatorReplacementGridRow17Seg09

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_17_y_20_fixed :
    FixedYReceipt 17 ⟨20, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_17_y_20 : RowBandReceipt 17 20 21 :=
  fixedYReceipt_to_rowBand 17 ⟨20, by decide⟩ receipt_row_17_y_20_fixed

private theorem receipt_row_17_y_21_fixed :
    FixedYReceipt 17 ⟨21, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_17_y_21 : RowBandReceipt 17 21 22 :=
  fixedYReceipt_to_rowBand 17 ⟨21, by decide⟩ receipt_row_17_y_21_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
