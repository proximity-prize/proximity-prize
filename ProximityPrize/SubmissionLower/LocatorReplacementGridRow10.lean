import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000




private theorem receipt_row_10_y00_t00_24_fixed :
    FixedYReceipt 10 ⟨0, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_10_y00_t00_24 : RowTileReceipt 10 0 1 0 24 :=
  fixedYReceipt_to_rowTile 10 ⟨0, by decide⟩ 0 24 receipt_row_10_y00_t00_24_fixed

private theorem receipt_row_10_y00_t24_26_fixed :
    FixedYReceipt 10 ⟨0, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_10_y00_t24_26 : RowTileReceipt 10 0 1 24 26 :=
  fixedYReceipt_to_rowTile 10 ⟨0, by decide⟩ 24 26 receipt_row_10_y00_t24_26_fixed

private theorem receipt_row_10_y01_t00_24_fixed :
    FixedYReceipt 10 ⟨1, by decide⟩ 0 24 := by decide +kernel

theorem receipt_row_10_y01_t00_24 : RowTileReceipt 10 1 2 0 24 :=
  fixedYReceipt_to_rowTile 10 ⟨1, by decide⟩ 0 24 receipt_row_10_y01_t00_24_fixed

private theorem receipt_row_10_y01_t24_26_fixed :
    FixedYReceipt 10 ⟨1, by decide⟩ 24 26 := by decide +kernel

theorem receipt_row_10_y01_t24_26 : RowTileReceipt 10 1 2 24 26 :=
  fixedYReceipt_to_rowTile 10 ⟨1, by decide⟩ 24 26 receipt_row_10_y01_t24_26_fixed





private theorem receipt_row_10_y02_t00_08_fixed :
    FixedYReceipt 10 ⟨2, by decide⟩ 0 8 := by decide +kernel

theorem receipt_row_10_y02_t00_08 : RowTileReceipt 10 2 3 0 8 :=
  fixedYReceipt_to_rowTile 10 ⟨2, by decide⟩ 0 8 receipt_row_10_y02_t00_08_fixed

private theorem receipt_row_10_y02_t08_26_fixed :
    FixedYReceipt 10 ⟨2, by decide⟩ 8 26 := by decide +kernel

theorem receipt_row_10_y02_t08_26 : RowTileReceipt 10 2 3 8 26 :=
  fixedYReceipt_to_rowTile 10 ⟨2, by decide⟩ 8 26 receipt_row_10_y02_t08_26_fixed

theorem receipt_row_10_band_03_05 : RowBandReceipt 10 3 5 := by decide +kernel





theorem receipt_row_10_band_05_07 : RowBandReceipt 10 5 7 := by decide +kernel

theorem receipt_row_10_band_07_09 : RowBandReceipt 10 7 9 := by decide +kernel





theorem receipt_row_10_band_09_11 : RowBandReceipt 10 9 11 := by decide +kernel

theorem receipt_row_10_band_11_13 : RowBandReceipt 10 11 13 := by decide +kernel





theorem receipt_row_10_band_13_15 : RowBandReceipt 10 13 15 := by decide +kernel

theorem receipt_row_10_band_15_17 : RowBandReceipt 10 15 17 := by decide +kernel





theorem receipt_row_10_band_17_19 : RowBandReceipt 10 17 19 := by decide +kernel

theorem receipt_row_10_band_19_23 : RowBandReceipt 10 19 23 := by decide +kernel





theorem receipt_row_10_y00_full : RowTileReceipt 10 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_10_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_10_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_10_band_00_01 : RowBandReceipt 10 0 1 :=
  rowTileFull_to_rowBand 10 0 receipt_row_10_y00_full

theorem receipt_row_10_y01_full : RowTileReceipt 10 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_10_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_10_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_10_band_01_02 : RowBandReceipt 10 1 2 :=
  rowTileFull_to_rowBand 10 1 receipt_row_10_y01_full

theorem receipt_row_10_y02_full : RowTileReceipt 10 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_10_y02_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_10_y02_t08_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_10_band_02_03 : RowBandReceipt 10 2 3 :=
  rowTileFull_to_rowBand 10 2 receipt_row_10_y02_full

private theorem receipt_row_10_fast : FastRowReceipt 10 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_10_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_10_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_10_band_02_03 cy (by omega) h_3
  by_cases h_5 : cy.val < 5
  · exact receipt_row_10_band_03_05 cy (by omega) h_5
  by_cases h_7 : cy.val < 7
  · exact receipt_row_10_band_05_07 cy (by omega) h_7
  by_cases h_9 : cy.val < 9
  · exact receipt_row_10_band_07_09 cy (by omega) h_9
  by_cases h_11 : cy.val < 11
  · exact receipt_row_10_band_09_11 cy (by omega) h_11
  by_cases h_13 : cy.val < 13
  · exact receipt_row_10_band_11_13 cy (by omega) h_13
  by_cases h_15 : cy.val < 15
  · exact receipt_row_10_band_13_15 cy (by omega) h_15
  by_cases h_17 : cy.val < 17
  · exact receipt_row_10_band_15_17 cy (by omega) h_17
  by_cases h_19 : cy.val < 19
  · exact receipt_row_10_band_17_19 cy (by omega) h_19
  · exact receipt_row_10_band_19_23 cy (by omega) (by omega)

theorem receipt_row_10 : RowReceipt 10 :=
  fastRowReceipt_to_rowReceipt 10 receipt_row_10_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
