import ProximityPrize.SubmissionLower.LocatorReplacementGridRow12Seg00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_12_y_02_fixed :
    FixedYReceipt 12 ⟨2, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_12_y_02 : RowBandReceipt 12 2 3 :=
  fixedYReceipt_to_rowBand 12 ⟨2, by decide⟩ receipt_row_12_y_02_fixed

private theorem receipt_row_12_y_03_fixed :
    FixedYReceipt 12 ⟨3, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_12_y_03 : RowBandReceipt 12 3 4 :=
  fixedYReceipt_to_rowBand 12 ⟨3, by decide⟩ receipt_row_12_y_03_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
