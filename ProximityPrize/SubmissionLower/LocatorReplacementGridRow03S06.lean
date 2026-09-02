import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03_band_15_17 : RowBandReceipt 3 15 17 := by decide +kernel

theorem receipt_row_03_band_17_19 : RowBandReceipt 3 17 19 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
