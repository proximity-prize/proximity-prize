import ProximityPrize.SubmissionLower.LocatorReplacementGridRow17Seg06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_17_y_14_fixed :
    FixedYReceipt 17 ⟨14, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_17_y_14 : RowBandReceipt 17 14 15 :=
  fixedYReceipt_to_rowBand 17 ⟨14, by decide⟩ receipt_row_17_y_14_fixed

private theorem receipt_row_17_y_15_fixed :
    FixedYReceipt 17 ⟨15, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_17_y_15 : RowBandReceipt 17 15 16 :=
  fixedYReceipt_to_rowBand 17 ⟨15, by decide⟩ receipt_row_17_y_15_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
