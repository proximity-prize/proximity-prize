import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_05_t_07_b : RowTileReceipt 7 7 8 17 18 := by decide +kernel

theorem receipt_row_07_band_05_t_07_c : RowTileReceipt 7 7 8 18 19 := by decide +kernel

theorem receipt_row_07_band_05_t_07_d : RowTileReceipt 7 7 8 19 20 := by decide +kernel

theorem receipt_row_07_band_05_t_07_e : RowTileReceipt 7 7 8 20 21 := by decide +kernel

theorem receipt_row_07_band_05_t_07_f : RowTileReceipt 7 7 8 21 22 := by decide +kernel

theorem receipt_row_07_band_05_t_07 : RowTileReceipt 7 7 8 16 22 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h_17 : ct.val < 17
  · exact receipt_row_07_band_05_t_07_a cy hylo hyhi ct htlo h_17
  by_cases h_18 : ct.val < 18
  · exact receipt_row_07_band_05_t_07_b cy hylo hyhi ct (by omega) h_18
  by_cases h_19 : ct.val < 19
  · exact receipt_row_07_band_05_t_07_c cy hylo hyhi ct (by omega) h_19
  by_cases h_20 : ct.val < 20
  · exact receipt_row_07_band_05_t_07_d cy hylo hyhi ct (by omega) h_20
  by_cases h_21 : ct.val < 21
  · exact receipt_row_07_band_05_t_07_e cy hylo hyhi ct (by omega) h_21
  · exact receipt_row_07_band_05_t_07_f cy hylo hyhi ct (by omega) hthi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
