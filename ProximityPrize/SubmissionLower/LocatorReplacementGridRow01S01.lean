import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_01_band_02_04 : RowBandReceipt 1 2 4 := by decide +kernel

theorem receipt_row_01_band_04_06 : RowBandReceipt 1 4 6 := by decide +kernel


end ProximityPrize.SubmissionLower.LocatorReplacementGridData
