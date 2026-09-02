import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_01_band_06_08 : RowBandReceipt 1 6 8 := by decide +kernel

theorem receipt_row_01_band_08_10 : RowBandReceipt 1 8 10 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
