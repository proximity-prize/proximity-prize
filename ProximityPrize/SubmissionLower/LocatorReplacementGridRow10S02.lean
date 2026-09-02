import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_10_band_05_07 : RowBandReceipt 10 5 7 := by decide +kernel

theorem receipt_row_10_band_07_09 : RowBandReceipt 10 7 9 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
