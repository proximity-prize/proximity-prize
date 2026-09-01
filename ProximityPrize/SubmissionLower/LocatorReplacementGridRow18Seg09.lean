import ProximityPrize.SubmissionLower.LocatorReplacementGridRow18Seg08

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_18_y_18_fixed :
    FixedYReceipt 18 ⟨18, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_18_y_18 : RowBandReceipt 18 18 19 :=
  fixedYReceipt_to_rowBand 18 ⟨18, by decide⟩ receipt_row_18_y_18_fixed

private theorem receipt_row_18_y_19_fixed :
    FixedYReceipt 18 ⟨19, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_18_y_19 : RowBandReceipt 18 19 20 :=
  fixedYReceipt_to_rowBand 18 ⟨19, by decide⟩ receipt_row_18_y_19_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
