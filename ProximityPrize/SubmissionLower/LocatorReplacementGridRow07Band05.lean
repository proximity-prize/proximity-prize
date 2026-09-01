import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Band05T07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_05 : RowBandReceipt 7 7 8 := by
  intro cy hylo hyhi ct
  by_cases h_1 : ct.val < 1
  · exact receipt_row_07_band_05_t_00 cy hylo hyhi ct (by omega) h_1
  by_cases h_2 : ct.val < 2
  · exact receipt_row_07_band_05_t_01 cy hylo hyhi ct (by omega) h_2
  by_cases h_3 : ct.val < 3
  · exact receipt_row_07_band_05_t_02 cy hylo hyhi ct (by omega) h_3
  by_cases h_4 : ct.val < 4
  · exact receipt_row_07_band_05_t_03 cy hylo hyhi ct (by omega) h_4
  by_cases h_5 : ct.val < 5
  · exact receipt_row_07_band_05_t_04 cy hylo hyhi ct (by omega) h_5
  by_cases h_10 : ct.val < 10
  · exact receipt_row_07_band_05_t_05 cy hylo hyhi ct (by omega) h_10
  by_cases h_16 : ct.val < 16
  · exact receipt_row_07_band_05_t_06 cy hylo hyhi ct (by omega) h_16
  · exact receipt_row_07_band_05_t_07 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
