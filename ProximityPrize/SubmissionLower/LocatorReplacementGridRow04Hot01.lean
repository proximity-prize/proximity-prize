import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_04_band_01_y_09_fixed :
    FixedYReceipt 4 ⟨9, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_01_y_09 : RowBandReceipt 4 9 10 :=
  fixedYReceipt_to_rowBand 4 ⟨9, by decide⟩ receipt_row_04_band_01_y_09_fixed

private theorem receipt_row_04_band_01_y_10_fixed :
    FixedYReceipt 4 ⟨10, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_01_y_10 : RowBandReceipt 4 10 11 :=
  fixedYReceipt_to_rowBand 4 ⟨10, by decide⟩ receipt_row_04_band_01_y_10_fixed

private theorem receipt_row_04_band_01_y_11_fixed :
    FixedYReceipt 4 ⟨11, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_04_band_01_y_11 : RowBandReceipt 4 11 12 :=
  fixedYReceipt_to_rowBand 4 ⟨11, by decide⟩ receipt_row_04_band_01_y_11_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
