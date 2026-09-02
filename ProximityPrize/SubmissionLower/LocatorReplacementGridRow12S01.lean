import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_12_band_04_06 : RowBandReceipt 12 4 6 := by decide +kernel

theorem receipt_row_12_band_06_08 : RowBandReceipt 12 6 8 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
