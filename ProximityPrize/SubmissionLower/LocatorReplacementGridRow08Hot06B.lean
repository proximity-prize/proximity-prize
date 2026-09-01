import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_10 : RowBandReceipt 8 12 13 := by decide +kernel

theorem receipt_row_08_band_11 : RowBandReceipt 8 13 14 := by decide +kernel

theorem receipt_row_08_band_12 : RowBandReceipt 8 14 22 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
