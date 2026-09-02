import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_01_band_18_20 : RowBandReceipt 1 18 20 := by decide +kernel

theorem receipt_row_01_band_20_22 : RowBandReceipt 1 20 22 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
