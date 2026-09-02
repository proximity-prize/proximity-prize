import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_06_t_00_a : RowTileReceipt 6 8 9 0 2 := by decide +kernel

theorem receipt_row_06_band_06_t_00_b : RowTileReceipt 6 8 9 2 4 := by decide +kernel

theorem receipt_row_06_band_06_t_00 : RowTileReceipt 6 8 9 0 4 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h_2 : ct.val < 2
  · exact receipt_row_06_band_06_t_00_a cy hylo hyhi ct htlo h_2
  · exact receipt_row_06_band_06_t_00_b cy hylo hyhi ct (by omega) hthi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
