import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_band_04_t_03_a1_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 4 5 := by decide +kernel

theorem receipt_row_08_band_04_t_03_a1 : RowTileReceipt 8 6 7 4 5 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 4 5
    receipt_row_08_band_04_t_03_a1_fixed

theorem receipt_row_08_band_04_t_03_a : RowTileReceipt 8 6 7 3 5 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 4
  · exact receipt_row_08_band_04_t_03_a0 cy hylo hyhi ct htlo h
  · exact receipt_row_08_band_04_t_03_a1 cy hylo hyhi ct (by omega) hthi

private theorem receipt_row_08_band_04_t_03_b0_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 5 6 := by decide +kernel

theorem receipt_row_08_band_04_t_03_b0 : RowTileReceipt 8 6 7 5 6 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 5 6
    receipt_row_08_band_04_t_03_b0_fixed

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
