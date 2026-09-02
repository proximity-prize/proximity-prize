import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_00_band_19_21 : RowBandReceipt 0 19 21 := by decide +kernel

theorem receipt_row_00_band_21_23 : RowBandReceipt 0 21 23 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
