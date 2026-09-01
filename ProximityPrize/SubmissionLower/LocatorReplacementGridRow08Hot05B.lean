import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_05 : RowBandReceipt 8 7 8 := by decide +kernel

theorem receipt_row_08_band_06 : RowBandReceipt 8 8 9 := by decide +kernel

theorem receipt_row_08_band_07 : RowBandReceipt 8 9 10 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
