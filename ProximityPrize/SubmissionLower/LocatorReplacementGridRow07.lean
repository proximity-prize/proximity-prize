import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_00 : RowBandReceipt 7 0 3 := by decide +kernel

theorem receipt_row_07_band_01 : RowBandReceipt 7 3 4 := by decide +kernel

theorem receipt_row_07_band_02 : RowBandReceipt 7 4 5 := by decide +kernel

theorem receipt_row_07_band_03 : RowBandReceipt 7 5 6 := by decide +kernel

theorem receipt_row_07_band_04_t_00 : RowTileReceipt 7 6 7 0 1 := by decide +kernel

theorem receipt_row_07_band_04_t_01 : RowTileReceipt 7 6 7 1 2 := by decide +kernel

theorem receipt_row_07_band_04_t_02 : RowTileReceipt 7 6 7 2 6 := by decide +kernel

theorem receipt_row_07_band_04_t_03 : RowTileReceipt 7 6 7 6 10 := by decide +kernel

theorem receipt_row_07_band_04_t_04 : RowTileReceipt 7 6 7 10 14 := by decide +kernel

theorem receipt_row_07_band_04_t_05 : RowTileReceipt 7 6 7 14 18 := by decide +kernel

theorem receipt_row_07_band_04_t_06 : RowTileReceipt 7 6 7 18 22 := by decide +kernel

theorem receipt_row_07_band_04 : RowBandReceipt 7 6 7 := by
  intro cy hylo hyhi ct
  by_cases h_1 : ct.val < 1
  · exact receipt_row_07_band_04_t_00 cy hylo hyhi ct (by omega) h_1
  by_cases h_2 : ct.val < 2
  · exact receipt_row_07_band_04_t_01 cy hylo hyhi ct (by omega) h_2
  by_cases h_6 : ct.val < 6
  · exact receipt_row_07_band_04_t_02 cy hylo hyhi ct (by omega) h_6
  by_cases h_10 : ct.val < 10
  · exact receipt_row_07_band_04_t_03 cy hylo hyhi ct (by omega) h_10
  by_cases h_14 : ct.val < 14
  · exact receipt_row_07_band_04_t_04 cy hylo hyhi ct (by omega) h_14
  by_cases h_18 : ct.val < 18
  · exact receipt_row_07_band_04_t_05 cy hylo hyhi ct (by omega) h_18
  · exact receipt_row_07_band_04_t_06 cy hylo hyhi ct (by omega) (by omega)

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

theorem receipt_row_07_band_06 : RowBandReceipt 7 8 9 := by decide +kernel

theorem receipt_row_07_band_07 : RowBandReceipt 7 9 10 := by decide +kernel

theorem receipt_row_07_band_08 : RowBandReceipt 7 10 11 := by decide +kernel

theorem receipt_row_07_band_09 : RowBandReceipt 7 11 12 := by decide +kernel

theorem receipt_row_07_band_10 : RowBandReceipt 7 12 13 := by decide +kernel

theorem receipt_row_07_band_11 : RowBandReceipt 7 13 14 := by decide +kernel

theorem receipt_row_07_band_12 : RowBandReceipt 7 14 21 := by decide +kernel

theorem receipt_row_07 : RowReceipt 7 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_07_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_07_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_07_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_07_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_07_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_07_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_07_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_07_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_07_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_07_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_07_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_07_band_11 cy (by omega) h_14
  · exact receipt_row_07_band_12 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
