import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_01_band_14_16 : RowBandReceipt 1 14 16 := by decide +kernel

theorem receipt_row_01_band_16_18 : RowBandReceipt 1 16 18 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
