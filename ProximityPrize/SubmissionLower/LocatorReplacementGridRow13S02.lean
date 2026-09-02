import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_13_band_08_10 : RowBandReceipt 13 8 10 := by decide +kernel

theorem receipt_row_13_band_10_12 : RowBandReceipt 13 10 12 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
