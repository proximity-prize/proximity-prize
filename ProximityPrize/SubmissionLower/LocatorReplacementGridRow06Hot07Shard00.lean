import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_12_y_19_fixed :
    FixedYReceipt 6 ⟨19, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_band_12_y_19 : RowBandReceipt 6 19 20 :=
  fixedYReceipt_to_rowBand 6 ⟨19, by decide⟩ receipt_row_06_band_12_y_19_fixed

private theorem receipt_row_06_band_12_y_20_fixed :
    FixedYReceipt 6 ⟨20, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_band_12_y_20 : RowBandReceipt 6 20 21 :=
  fixedYReceipt_to_rowBand 6 ⟨20, by decide⟩ receipt_row_06_band_12_y_20_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
