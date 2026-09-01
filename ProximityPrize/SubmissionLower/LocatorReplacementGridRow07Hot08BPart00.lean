import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot08

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_12_a : RowBandReceipt 7 14 16 := by decide +kernel

theorem receipt_row_07_band_12_b : RowBandReceipt 7 16 18 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
