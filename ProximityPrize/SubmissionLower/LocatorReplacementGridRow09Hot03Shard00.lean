import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Hot02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_band_05 : RowBandReceipt 9 7 8 := by decide +kernel

theorem receipt_row_09_band_06 : RowBandReceipt 9 8 9 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
