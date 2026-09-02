import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_18_band_12_14 : RowBandReceipt 18 12 14 := by decide +kernel

theorem receipt_row_18_band_14_16 : RowBandReceipt 18 14 16 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
