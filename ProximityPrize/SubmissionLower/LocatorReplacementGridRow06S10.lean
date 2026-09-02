import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_17_19 : RowBandReceipt 6 17 19 := by decide +kernel

theorem receipt_row_06_band_19_21 : RowBandReceipt 6 19 21 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
