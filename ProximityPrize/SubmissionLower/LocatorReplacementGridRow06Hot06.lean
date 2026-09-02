import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot06Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_06_band_12_y_18_fixed :
    FixedYReceipt 6 ⟨18, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_06_band_12_y_18 : RowBandReceipt 6 18 19 :=
  fixedYReceipt_to_rowBand 6 ⟨18, by decide⟩ receipt_row_06_band_12_y_18_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
