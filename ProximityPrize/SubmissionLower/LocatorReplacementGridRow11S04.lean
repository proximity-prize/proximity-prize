import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_11_band_16_18 : RowBandReceipt 11 16 18 := by decide +kernel

theorem receipt_row_11_band_18_23 : RowBandReceipt 11 18 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
