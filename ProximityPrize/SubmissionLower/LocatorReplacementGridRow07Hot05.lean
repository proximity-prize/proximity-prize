import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot04

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_05_t_06_c : RowTileReceipt 7 7 8 12 13 := by decide +kernel

theorem receipt_row_07_band_05_t_06_d : RowTileReceipt 7 7 8 13 14 := by decide +kernel

theorem receipt_row_07_band_05_t_06_e : RowTileReceipt 7 7 8 14 15 := by decide +kernel

theorem receipt_row_07_band_05_t_06_f : RowTileReceipt 7 7 8 15 16 := by decide +kernel

theorem receipt_row_07_band_05_t_06 : RowTileReceipt 7 7 8 10 16 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h_11 : ct.val < 11
  · exact receipt_row_07_band_05_t_06_a cy hylo hyhi ct htlo h_11
  by_cases h_12 : ct.val < 12
  · exact receipt_row_07_band_05_t_06_b cy hylo hyhi ct (by omega) h_12
  by_cases h_13 : ct.val < 13
  · exact receipt_row_07_band_05_t_06_c cy hylo hyhi ct (by omega) h_13
  by_cases h_14 : ct.val < 14
  · exact receipt_row_07_band_05_t_06_d cy hylo hyhi ct (by omega) h_14
  by_cases h_15 : ct.val < 15
  · exact receipt_row_07_band_05_t_06_e cy hylo hyhi ct (by omega) h_15
  · exact receipt_row_07_band_05_t_06_f cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_05_t_07_a : RowTileReceipt 7 7 8 16 17 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
