import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_11 : RowBandReceipt 9 13 14 := by decide +kernel

private theorem receipt_row_09_band_12_y_14_fixed : FixedYReceipt 9 ⟨14, by decide⟩ 0 23 := by decide +kernel
theorem receipt_row_09_band_12_y_14 : RowBandReceipt 9 14 15 :=
  fixedYReceipt_to_rowBand 9 ⟨14, by decide⟩ receipt_row_09_band_12_y_14_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
