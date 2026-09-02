import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03_band_19_21 : RowBandReceipt 3 19 21 := by decide +kernel

theorem receipt_row_03_band_21_23 : RowBandReceipt 3 21 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
