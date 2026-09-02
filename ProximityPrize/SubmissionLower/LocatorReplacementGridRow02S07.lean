import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_02_band_20_22 : RowBandReceipt 2 20 22 := by decide +kernel

theorem receipt_row_02_band_22_23 : RowBandReceipt 2 22 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
