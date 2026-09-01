import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg08

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_y_18_fixed :
    FixedYReceipt 13 ⟨18, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y_18 : RowBandReceipt 13 18 19 :=
  fixedYReceipt_to_rowBand 13 ⟨18, by decide⟩ receipt_row_13_y_18_fixed

private theorem receipt_row_13_y_19_fixed :
    FixedYReceipt 13 ⟨19, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_13_y_19 : RowBandReceipt 13 19 20 :=
  fixedYReceipt_to_rowBand 13 ⟨19, by decide⟩ receipt_row_13_y_19_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
