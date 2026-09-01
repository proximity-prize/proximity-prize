import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07A

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_05_t_00 : RowTileReceipt 7 7 8 0 1 := by decide +kernel

theorem receipt_row_07_band_05_t_01 : RowTileReceipt 7 7 8 1 2 := by decide +kernel

theorem receipt_row_07_band_05_t_02 : RowTileReceipt 7 7 8 2 3 := by decide +kernel

theorem receipt_row_07_band_05_t_03 : RowTileReceipt 7 7 8 3 4 := by decide +kernel

theorem receipt_row_07_band_05_t_04 : RowTileReceipt 7 7 8 4 5 := by decide +kernel

private theorem receipt_row_07_band_05_t_05_a_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 5 7 := by decide +kernel

theorem receipt_row_07_band_05_t_05_a : RowTileReceipt 7 7 8 5 7 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 5 7
    receipt_row_07_band_05_t_05_a_fixed

private theorem receipt_row_07_band_05_t_05_b_fixed :
    FixedYReceipt 7 ⟨7, by decide⟩ 7 10 := by decide +kernel

theorem receipt_row_07_band_05_t_05_b : RowTileReceipt 7 7 8 7 10 :=
  fixedYReceipt_to_rowTile 7 ⟨7, by decide⟩ 7 10
    receipt_row_07_band_05_t_05_b_fixed

theorem receipt_row_07_band_05_t_05 : RowTileReceipt 7 7 8 5 10 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 7
  · exact receipt_row_07_band_05_t_05_a cy hylo hyhi ct htlo h
  · exact receipt_row_07_band_05_t_05_b cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_05_t_06 : RowTileReceipt 7 7 8 10 16 := by decide +kernel

theorem receipt_row_07_band_05_t_07 : RowTileReceipt 7 7 8 16 22 := by decide +kernel

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

theorem receipt_row_07_band_08 : RowBandReceipt 7 10 11 := by decide +kernel

theorem receipt_row_07_band_09 : RowBandReceipt 7 11 12 := by decide +kernel

theorem receipt_row_07_band_10 : RowBandReceipt 7 12 13 := by decide +kernel

theorem receipt_row_07_band_11 : RowBandReceipt 7 13 14 := by decide +kernel

theorem receipt_row_07_band_12 : RowBandReceipt 7 14 22 := by decide +kernel

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
