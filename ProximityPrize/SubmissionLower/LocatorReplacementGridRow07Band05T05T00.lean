import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Band05T05T00T01
namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_row_07_band_05_t_05_t_00 : RowTileReceipt 7 7 8 5 7 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 6
  · exact receipt_row_07_band_05_t_05_t_00_t_00 cy hylo hyhi ct htlo h
  · exact receipt_row_07_band_05_t_05_t_00_t_01 cy hylo hyhi ct (by omega) hthi
end ProximityPrize.SubmissionLower.LocatorReplacementGridData
