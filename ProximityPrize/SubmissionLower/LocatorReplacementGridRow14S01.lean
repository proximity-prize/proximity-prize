import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_14_band_04_06 : RowBandReceipt 14 4 6 := by decide +kernel

theorem receipt_row_14_band_06_08 : RowBandReceipt 14 6 8 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
