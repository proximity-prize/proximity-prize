import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_00 : RowBandReceipt 6 0 3 := by decide +kernel

theorem receipt_row_06_band_01 : RowBandReceipt 6 3 4 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
