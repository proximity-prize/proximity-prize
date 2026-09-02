import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_00_band_03_05 : RowBandReceipt 0 3 5 := by decide +kernel

theorem receipt_row_00_band_05_07 : RowBandReceipt 0 5 7 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
