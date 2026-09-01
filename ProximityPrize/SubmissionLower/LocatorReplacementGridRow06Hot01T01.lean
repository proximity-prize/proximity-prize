import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Hot01T01C07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_06_t_01 : RowTileReceipt 6 8 9 4 8 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h₅ : ct.val < 5
  · exact receipt_row_06_band_06_t_01_c_04 cy hylo hyhi ct htlo h₅
  by_cases h₆ : ct.val < 6
  · exact receipt_row_06_band_06_t_01_c_05 cy hylo hyhi ct (by omega) h₆
  by_cases h₇ : ct.val < 7
  · exact receipt_row_06_band_06_t_01_c_06 cy hylo hyhi ct (by omega) h₇
  · exact receipt_row_06_band_06_t_01_c_07 cy hylo hyhi ct (by omega) hthi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
