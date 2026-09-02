import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02Y14

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_band_02_y_15_fixed :
    FixedYReceipt 3 ⟨15, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_band_02_y_15 : RowBandReceipt 3 15 16 :=
  fixedYReceipt_to_rowBand 3 ⟨15, by decide⟩ receipt_row_03_band_02_y_15_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
