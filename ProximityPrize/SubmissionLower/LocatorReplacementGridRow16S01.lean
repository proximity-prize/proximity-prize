import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_16_band_04_06 : RowBandReceipt 16 4 6 := by decide +kernel

theorem receipt_row_16_band_06_08 : RowBandReceipt 16 6 8 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
