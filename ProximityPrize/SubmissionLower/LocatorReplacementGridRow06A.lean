import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Core

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_00 : RowBandReceipt 6 0 3 := by decide +kernel

theorem receipt_row_06_band_01 : RowBandReceipt 6 3 4 := by decide +kernel

theorem receipt_row_06_band_02 : RowBandReceipt 6 4 5 := by decide +kernel

theorem receipt_row_06_band_03 : RowBandReceipt 6 5 6 := by decide +kernel

theorem receipt_row_06_band_04 : RowBandReceipt 6 6 7 := by decide +kernel

theorem receipt_row_06_band_05 : RowBandReceipt 6 7 8 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
