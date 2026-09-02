import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_11 : RowBandReceipt 6 13 14 := by decide +kernel

private theorem receipt_row_06_band_12_y_14_fixed :
    FixedYReceipt 6 ⟨14, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_band_12_y_14 : RowBandReceipt 6 14 15 :=
  fixedYReceipt_to_rowBand 6 ⟨14, by decide⟩ receipt_row_06_band_12_y_14_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
