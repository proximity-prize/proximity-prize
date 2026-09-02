import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_16_18 : RowBandReceipt 5 16 18 := by decide +kernel

theorem receipt_row_05_band_18_20 : RowBandReceipt 5 18 20 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
