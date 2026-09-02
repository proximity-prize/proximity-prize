import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_00_band_11_13 : RowBandReceipt 0 11 13 := by decide +kernel

theorem receipt_row_00_band_13_15 : RowBandReceipt 0 13 15 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
