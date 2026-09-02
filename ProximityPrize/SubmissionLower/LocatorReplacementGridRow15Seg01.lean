import ProximityPrize.SubmissionLower.LocatorReplacementGridRow15Seg00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_15_y_02_fixed :
    FixedYReceipt 15 ⟨2, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_15_y_02 : RowBandReceipt 15 2 3 :=
  fixedYReceipt_to_rowBand 15 ⟨2, by decide⟩ receipt_row_15_y_02_fixed

private theorem receipt_row_15_y_03_fixed :
    FixedYReceipt 15 ⟨3, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_15_y_03 : RowBandReceipt 15 3 4 :=
  fixedYReceipt_to_rowBand 15 ⟨3, by decide⟩ receipt_row_15_y_03_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
