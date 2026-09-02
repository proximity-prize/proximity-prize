import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_13_band_04_06 : RowBandReceipt 13 4 6 := by decide +kernel

theorem receipt_row_13_band_06_08 : RowBandReceipt 13 6 8 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
