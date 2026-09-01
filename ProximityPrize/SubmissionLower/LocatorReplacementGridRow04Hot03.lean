import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_02_y_14_fixed :
    FixedYReceipt 4 ⟨14, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_04_band_02_y_14 : RowBandReceipt 4 14 15 :=
  fixedYReceipt_to_rowBand 4 ⟨14, by decide⟩ receipt_row_04_band_02_y_14_fixed

private theorem receipt_row_04_band_02_y_15_fixed :
    FixedYReceipt 4 ⟨15, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_04_band_02_y_15 : RowBandReceipt 4 15 16 :=
  fixedYReceipt_to_rowBand 4 ⟨15, by decide⟩ receipt_row_04_band_02_y_15_fixed

private theorem receipt_row_04_band_02_y_16_fixed :
    FixedYReceipt 4 ⟨16, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_04_band_02_y_16 : RowBandReceipt 4 16 17 :=
  fixedYReceipt_to_rowBand 4 ⟨16, by decide⟩ receipt_row_04_band_02_y_16_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
