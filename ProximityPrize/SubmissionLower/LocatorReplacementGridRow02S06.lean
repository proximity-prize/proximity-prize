import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_02_band_16_18 : RowBandReceipt 2 16 18 := by decide +kernel

theorem receipt_row_02_band_18_20 : RowBandReceipt 2 18 20 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
