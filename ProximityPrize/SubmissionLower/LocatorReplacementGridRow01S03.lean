import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_01_band_10_12 : RowBandReceipt 1 10 12 := by decide +kernel

theorem receipt_row_01_band_12_14 : RowBandReceipt 1 12 14 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
