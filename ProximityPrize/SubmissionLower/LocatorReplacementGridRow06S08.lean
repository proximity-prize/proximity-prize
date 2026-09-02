import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_09_11 : RowBandReceipt 6 9 11 := by decide +kernel

theorem receipt_row_06_band_11_13 : RowBandReceipt 6 11 13 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
