import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y_12_fixed :
    FixedYReceipt 13 ⟨12, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_13_y_12 : RowBandReceipt 13 12 13 :=
  fixedYReceipt_to_rowBand 13 ⟨12, by decide⟩ receipt_row_13_y_12_fixed

private theorem receipt_row_13_y_13_fixed :
    FixedYReceipt 13 ⟨13, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_13_y_13 : RowBandReceipt 13 13 14 :=
  fixedYReceipt_to_rowBand 13 ⟨13, by decide⟩ receipt_row_13_y_13_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
