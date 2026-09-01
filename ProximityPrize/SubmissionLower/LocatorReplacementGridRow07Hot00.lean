import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_00 : RowBandReceipt 7 0 3 := by decide +kernel

theorem receipt_row_07_band_01 : RowBandReceipt 7 3 4 := by decide +kernel

theorem receipt_row_07_band_02 : RowBandReceipt 7 4 5 := by decide +kernel

theorem receipt_row_07_band_03 : RowBandReceipt 7 5 6 := by decide +kernel

theorem receipt_row_07_band_04_t_00 : RowTileReceipt 7 6 7 0 1 := by decide +kernel

theorem receipt_row_07_band_04_t_01 : RowTileReceipt 7 6 7 1 2 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
