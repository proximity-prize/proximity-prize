import ProximityPrize.SubmissionLower.LocatorReplacementGridRow14

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_17_y_00_fixed :
    FixedYReceipt 17 ⟨0, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_17_y_00 : RowBandReceipt 17 0 1 :=
  fixedYReceipt_to_rowBand 17 ⟨0, by decide⟩ receipt_row_17_y_00_fixed

private theorem receipt_row_17_y_01_fixed :
    FixedYReceipt 17 ⟨1, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_17_y_01 : RowBandReceipt 17 1 2 :=
  fixedYReceipt_to_rowBand 17 ⟨1, by decide⟩ receipt_row_17_y_01_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
