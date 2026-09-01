import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_band_05_t_05_b2_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 9 10 := by decide +kernel

theorem receipt_row_07_band_05_t_05_b2 : RowTileReceipt 7 7 8 9 10 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 9 10
    receipt_row_07_band_05_t_05_b2_fixed

theorem receipt_row_07_band_05_t_05_b : RowTileReceipt 7 7 8 7 10 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h_8 : ct.val < 8
  · exact receipt_row_07_band_05_t_05_b0 cy hylo hyhi ct htlo h_8
  by_cases h_9 : ct.val < 9
  · exact receipt_row_07_band_05_t_05_b1 cy hylo hyhi ct (by omega) h_9
  · exact receipt_row_07_band_05_t_05_b2 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_05_t_05 : RowTileReceipt 7 7 8 5 10 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 7
  · exact receipt_row_07_band_05_t_05_a cy hylo hyhi ct htlo h
  · exact receipt_row_07_band_05_t_05_b cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_05_t_06_a : RowTileReceipt 7 7 8 10 11 := by decide +kernel

theorem receipt_row_07_band_05_t_06_b : RowTileReceipt 7 7 8 11 12 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
