import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_15_band_00_02 : RowBandReceipt 15 0 2 := by decide +kernel

theorem receipt_row_15_band_02_04 : RowBandReceipt 15 2 4 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
