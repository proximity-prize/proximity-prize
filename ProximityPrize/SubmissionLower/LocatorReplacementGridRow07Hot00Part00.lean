import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_00 : RowBandReceipt 7 0 3 := by decide +kernel

theorem receipt_row_07_band_01 : RowBandReceipt 7 3 4 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
