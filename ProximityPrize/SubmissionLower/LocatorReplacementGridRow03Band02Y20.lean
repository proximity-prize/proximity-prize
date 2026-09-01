import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02Y19

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_03_band_02_y_20_fixed :
    FixedYReceipt 3 ⟨20, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_03_band_02_y_20 : RowBandReceipt 3 20 21 :=
  fixedYReceipt_to_rowBand 3 ⟨20, by decide⟩ receipt_row_03_band_02_y_20_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
