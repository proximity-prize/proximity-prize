import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_band_00 : RowBandReceipt 8 0 3 := by decide +kernel

theorem receipt_row_08_band_01 : RowBandReceipt 8 3 4 := by decide +kernel

theorem receipt_row_08_band_02 : RowBandReceipt 8 4 5 := by decide +kernel

theorem receipt_row_08_band_03_t_00 : RowTileReceipt 8 5 6 0 1 := by decide +kernel

theorem receipt_row_08_band_03_t_01 : RowTileReceipt 8 5 6 1 2 := by decide +kernel

theorem receipt_row_08_band_03_t_02 : RowTileReceipt 8 5 6 2 3 := by decide +kernel

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

theorem receipt_row_08_band_04_t_00 : RowTileReceipt 8 6 7 0 1 := by decide +kernel

theorem receipt_row_08_band_04_t_01 : RowTileReceipt 8 6 7 1 2 := by decide +kernel

theorem receipt_row_08_band_04_t_02 : RowTileReceipt 8 6 7 2 3 := by decide +kernel

private theorem receipt_row_08_band_04_t_03_a_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 3 5 := by decide +kernel

theorem receipt_row_08_band_04_t_03_a : RowTileReceipt 8 6 7 3 5 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 3 5
    receipt_row_08_band_04_t_03_a_fixed

private theorem receipt_row_08_band_04_t_03_b_fixed :
    FixedYReceipt 8 ⟨6, by decide⟩ 5 8 := by decide +kernel

theorem receipt_row_08_band_04_t_03_b : RowTileReceipt 8 6 7 5 8 :=
  fixedYReceipt_to_rowTile 8 ⟨6, by decide⟩ 5 8
    receipt_row_08_band_04_t_03_b_fixed

theorem receipt_row_08_band_04_t_03 : RowTileReceipt 8 6 7 3 8 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h : ct.val < 5
  · exact receipt_row_08_band_04_t_03_a cy hylo hyhi ct htlo h
  · exact receipt_row_08_band_04_t_03_b cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_04_t_04 : RowTileReceipt 8 6 7 8 15 := by decide +kernel

theorem receipt_row_08_band_04_t_05 : RowTileReceipt 8 6 7 15 22 := by decide +kernel

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

theorem receipt_row_08_band_05 : RowBandReceipt 8 7 8 := by decide +kernel

theorem receipt_row_08_band_06 : RowBandReceipt 8 8 9 := by decide +kernel

theorem receipt_row_08_band_07 : RowBandReceipt 8 9 10 := by decide +kernel

theorem receipt_row_08_band_08 : RowBandReceipt 8 10 11 := by decide +kernel

theorem receipt_row_08_band_09 : RowBandReceipt 8 11 12 := by decide +kernel

theorem receipt_row_08_band_10 : RowBandReceipt 8 12 13 := by decide +kernel

theorem receipt_row_08_band_11 : RowBandReceipt 8 13 14 := by decide +kernel

theorem receipt_row_08_band_12 : RowBandReceipt 8 14 22 := by decide +kernel

theorem receipt_row_08 : RowReceipt 8 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_08_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_08_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_08_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_08_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_08_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_08_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_08_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_08_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_08_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_08_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_08_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_08_band_11 cy (by omega) h_14
  · exact receipt_row_08_band_12 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
