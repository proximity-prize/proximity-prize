import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_band_12_y_16_fixed : FixedYReceipt 9 ⟨16, by decide⟩ 0 22 := by decide +kernel
theorem receipt_row_09_band_12_y_16 : RowBandReceipt 9 16 17 :=
  fixedYReceipt_to_rowBand 9 ⟨16, by decide⟩ receipt_row_09_band_12_y_16_fixed

private theorem receipt_row_09_band_12_y_17_fixed : FixedYReceipt 9 ⟨17, by decide⟩ 0 22 := by decide +kernel
theorem receipt_row_09_band_12_y_17 : RowBandReceipt 9 17 18 :=
  fixedYReceipt_to_rowBand 9 ⟨17, by decide⟩ receipt_row_09_band_12_y_17_fixed

private theorem receipt_row_09_band_12_y_18_fixed : FixedYReceipt 9 ⟨18, by decide⟩ 0 22 := by decide +kernel
theorem receipt_row_09_band_12_y_18 : RowBandReceipt 9 18 19 :=
  fixedYReceipt_to_rowBand 9 ⟨18, by decide⟩ receipt_row_09_band_12_y_18_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
