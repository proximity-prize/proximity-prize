import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot00Part01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_04 : RowBandReceipt 6 6 7 := by decide +kernel

theorem receipt_row_06_band_05 : RowBandReceipt 6 7 8 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
