import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot07Shard00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_09_band_12_y_18_fixed : FixedYReceipt 9 ⟨18, by decide⟩ 0 23 := by decide +kernel
theorem receipt_row_09_band_12_y_18 : RowBandReceipt 9 18 19 :=
  fixedYReceipt_to_rowBand 9 ⟨18, by decide⟩ receipt_row_09_band_12_y_18_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
