import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot05Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_12_y_15_fixed :
    FixedYReceipt 6 ⟨15, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_band_12_y_15 : RowBandReceipt 6 15 16 :=
  fixedYReceipt_to_rowBand 6 ⟨15, by decide⟩ receipt_row_06_band_12_y_15_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
