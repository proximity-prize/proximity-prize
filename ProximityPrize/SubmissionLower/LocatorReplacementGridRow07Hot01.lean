import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_04_t_02 : RowTileReceipt 7 6 7 2 6 := by decide +kernel

theorem receipt_row_07_band_04_t_03 : RowTileReceipt 7 6 7 6 10 := by decide +kernel

theorem receipt_row_07_band_04_t_04 : RowTileReceipt 7 6 7 10 14 := by decide +kernel

theorem receipt_row_07_band_04_t_05 : RowTileReceipt 7 6 7 14 18 := by decide +kernel

theorem receipt_row_07_band_04_t_06 : RowTileReceipt 7 6 7 18 22 := by decide +kernel

theorem receipt_row_07_band_04 : RowBandReceipt 7 6 7 := by
  intro cy hylo hyhi ct
  by_cases h_1 : ct.val < 1
  · exact receipt_row_07_band_04_t_00 cy hylo hyhi ct (by omega) h_1
  by_cases h_2 : ct.val < 2
  · exact receipt_row_07_band_04_t_01 cy hylo hyhi ct (by omega) h_2
  by_cases h_6 : ct.val < 6
  · exact receipt_row_07_band_04_t_02 cy hylo hyhi ct (by omega) h_6
  by_cases h_10 : ct.val < 10
  · exact receipt_row_07_band_04_t_03 cy hylo hyhi ct (by omega) h_10
  by_cases h_14 : ct.val < 14
  · exact receipt_row_07_band_04_t_04 cy hylo hyhi ct (by omega) h_14
  by_cases h_18 : ct.val < 18
  · exact receipt_row_07_band_04_t_05 cy hylo hyhi ct (by omega) h_18
  · exact receipt_row_07_band_04_t_06 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
