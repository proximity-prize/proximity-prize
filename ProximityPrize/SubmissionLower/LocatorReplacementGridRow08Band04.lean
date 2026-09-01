import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Band04T05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_04 : RowBandReceipt 8 6 7 := by
  intro cy hylo hyhi ct
  by_cases h_1 : ct.val < 1
  · exact receipt_row_08_band_04_t_00 cy hylo hyhi ct (by omega) h_1
  by_cases h_2 : ct.val < 2
  · exact receipt_row_08_band_04_t_01 cy hylo hyhi ct (by omega) h_2
  by_cases h_3 : ct.val < 3
  · exact receipt_row_08_band_04_t_02 cy hylo hyhi ct (by omega) h_3
  by_cases h_8 : ct.val < 8
  · exact receipt_row_08_band_04_t_03 cy hylo hyhi ct (by omega) h_8
  by_cases h_15 : ct.val < 15
  · exact receipt_row_08_band_04_t_04 cy hylo hyhi ct (by omega) h_15
  · exact receipt_row_08_band_04_t_05 cy hylo hyhi ct (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
