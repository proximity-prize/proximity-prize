import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_11_y_00_fixed :
    FixedYReceipt 11 ⟨0, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_11_y_00 : RowBandReceipt 11 0 1 :=
  fixedYReceipt_to_rowBand 11 ⟨0, by decide⟩ receipt_row_11_y_00_fixed

private theorem receipt_row_11_y_01_fixed :
    FixedYReceipt 11 ⟨1, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_11_y_01 : RowBandReceipt 11 1 2 :=
  fixedYReceipt_to_rowBand 11 ⟨1, by decide⟩ receipt_row_11_y_01_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
