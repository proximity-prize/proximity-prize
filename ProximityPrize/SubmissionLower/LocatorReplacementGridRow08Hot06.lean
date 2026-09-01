import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot05B

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_08 : RowBandReceipt 8 10 11 := by decide +kernel

theorem receipt_row_08_band_09 : RowBandReceipt 8 11 12 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
