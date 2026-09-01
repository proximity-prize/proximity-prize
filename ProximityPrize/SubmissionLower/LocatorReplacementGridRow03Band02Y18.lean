import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02Y17

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_band_02_y_18_fixed :
    FixedYReceipt 3 ⟨18, by decide⟩ 0 23 := by decide +kernel

theorem receipt_row_03_band_02_y_18 : RowBandReceipt 3 18 19 :=
  fixedYReceipt_to_rowBand 3 ⟨18, by decide⟩ receipt_row_03_band_02_y_18_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
