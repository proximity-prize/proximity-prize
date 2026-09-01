import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_04_band_00 : RowBandReceipt 4 0 7 := by decide +kernel

private theorem receipt_row_04_band_01_y_07_fixed :
    FixedYReceipt 4 ⟨7, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_04_band_01_y_07 : RowBandReceipt 4 7 8 :=
  fixedYReceipt_to_rowBand 4 ⟨7, by decide⟩ receipt_row_04_band_01_y_07_fixed

private theorem receipt_row_04_band_01_y_08_fixed :
    FixedYReceipt 4 ⟨8, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_04_band_01_y_08 : RowBandReceipt 4 8 9 :=
  fixedYReceipt_to_rowBand 4 ⟨8, by decide⟩ receipt_row_04_band_01_y_08_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
