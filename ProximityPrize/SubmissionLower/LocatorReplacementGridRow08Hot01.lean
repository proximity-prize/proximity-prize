import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_03_t_03 : RowTileReceipt 8 5 6 3 7 := by decide +kernel

theorem receipt_row_08_band_03_t_04 : RowTileReceipt 8 5 6 7 11 := by decide +kernel

theorem receipt_row_08_band_03_t_05 : RowTileReceipt 8 5 6 11 15 := by decide +kernel

theorem receipt_row_08_band_03_t_06 : RowTileReceipt 8 5 6 15 19 := by decide +kernel

theorem receipt_row_08_band_03_t_07 : RowTileReceipt 8 5 6 19 22 := by decide +kernel

theorem receipt_row_08_band_03 : RowBandReceipt 8 5 6 := by
  intro cy hylo hyhi ct
  by_cases h_1 : ct.val < 1
  · exact receipt_row_08_band_03_t_00 cy hylo hyhi ct (by omega) h_1
  by_cases h_2 : ct.val < 2
  · exact receipt_row_08_band_03_t_01 cy hylo hyhi ct (by omega) h_2
  by_cases h_3 : ct.val < 3
  · exact receipt_row_08_band_03_t_02 cy hylo hyhi ct (by omega) h_3
  by_cases h_7 : ct.val < 7
  · exact receipt_row_08_band_03_t_03 cy hylo hyhi ct (by omega) h_7
  by_cases h_11 : ct.val < 11
  · exact receipt_row_08_band_03_t_04 cy hylo hyhi ct (by omega) h_11
  by_cases h_15 : ct.val < 15
  · exact receipt_row_08_band_03_t_05 cy hylo hyhi ct (by omega) h_15
  by_cases h_19 : ct.val < 19
  · exact receipt_row_08_band_03_t_06 cy hylo hyhi ct (by omega) h_19
  · exact receipt_row_08_band_03_t_07 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
