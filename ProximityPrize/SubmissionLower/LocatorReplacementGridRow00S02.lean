import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_00_band_07_09 : RowBandReceipt 0 7 9 := by decide +kernel

theorem receipt_row_00_band_09_11 : RowBandReceipt 0 9 11 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
