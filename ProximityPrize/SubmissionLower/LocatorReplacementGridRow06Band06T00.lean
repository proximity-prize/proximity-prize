import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Band06T00T03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_band_06_t_00 : RowTileReceipt 6 8 9 0 4 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h₀ : ct.val < 1
  · exact receipt_row_06_band_06_t_00_t_00 cy hylo hyhi ct htlo h₀
  by_cases h₁ : ct.val < 2
  · exact receipt_row_06_band_06_t_00_t_01 cy hylo hyhi ct (by omega) h₁
  by_cases h₂ : ct.val < 3
  · exact receipt_row_06_band_06_t_00_t_02 cy hylo hyhi ct (by omega) h₂
  · exact receipt_row_06_band_06_t_00_t_03 cy hylo hyhi ct (by omega) hthi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
