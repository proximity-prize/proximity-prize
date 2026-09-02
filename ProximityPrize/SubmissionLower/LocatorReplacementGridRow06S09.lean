import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_13_15 : RowBandReceipt 6 13 15 := by decide +kernel

theorem receipt_row_06_band_15_17 : RowBandReceipt 6 15 17 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
