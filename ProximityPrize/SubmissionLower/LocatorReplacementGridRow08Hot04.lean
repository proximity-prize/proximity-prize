import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot03

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_band_04_t_03_b1_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 6 7 := by decide +kernel

theorem receipt_row_08_band_04_t_03_b1 : RowTileReceipt 8 6 7 6 7 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 6 7
    receipt_row_08_band_04_t_03_b1_fixed

private theorem receipt_row_08_band_04_t_03_b2_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 7 8 := by decide +kernel

theorem receipt_row_08_band_04_t_03_b2 : RowTileReceipt 8 6 7 7 8 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 7 8
    receipt_row_08_band_04_t_03_b2_fixed

theorem receipt_row_08_band_04_t_03_b : RowTileReceipt 8 6 7 5 8 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h₆ : ct.val < 6
  · exact receipt_row_08_band_04_t_03_b0 cy hylo hyhi ct htlo h₆
  by_cases h₇ : ct.val < 7
  · exact receipt_row_08_band_04_t_03_b1 cy hylo hyhi ct (by omega) h₇
  · exact receipt_row_08_band_04_t_03_b2 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_04_t_03 : RowTileReceipt 8 6 7 3 8 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 5
  · exact receipt_row_08_band_04_t_03_a cy hylo hyhi ct htlo h
  · exact receipt_row_08_band_04_t_03_b cy hylo hyhi ct (by omega) hthi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
