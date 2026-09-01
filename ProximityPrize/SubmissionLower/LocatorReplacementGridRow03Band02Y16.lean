import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02Y15

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_band_02_y_16_fixed :
    FixedYReceipt 3 ⟨16, by decide⟩ 0 22 := by decide +kernel

theorem receipt_row_03_band_02_y_16 : RowBandReceipt 3 16 17 :=
  fixedYReceipt_to_rowBand 3 ⟨16, by decide⟩ receipt_row_03_band_02_y_16_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
