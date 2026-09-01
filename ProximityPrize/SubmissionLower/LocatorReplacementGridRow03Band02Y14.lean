import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_band_02_y_14_fixed :
    FixedYReceipt 3 ⟨14, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_03_band_02_y_14 : RowBandReceipt 3 14 15 :=
  fixedYReceipt_to_rowBand 3 ⟨14, by decide⟩ receipt_row_03_band_02_y_14_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
