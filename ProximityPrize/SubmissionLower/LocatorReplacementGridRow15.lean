import ProximityPrize.SubmissionLower.LocatorReplacementGridRow15S00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_15_y00_full : RowTileReceipt 15 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_15_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_15_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_15_band_00_01 : RowBandReceipt 15 0 1 :=
  rowTileFull_to_rowBand 15 0 receipt_row_15_y00_full

theorem receipt_row_15_y01_full : RowTileReceipt 15 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_15_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_15_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_15_band_01_02 : RowBandReceipt 15 1 2 :=
  rowTileFull_to_rowBand 15 1 receipt_row_15_y01_full

theorem receipt_row_15_y02_full : RowTileReceipt 15 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_15_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_15_y02_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_15_band_02_03 : RowBandReceipt 15 2 3 :=
  rowTileFull_to_rowBand 15 2 receipt_row_15_y02_full

theorem receipt_row_15_y03_full : RowTileReceipt 15 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_15_y03_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_15_y03_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_15_band_03_04 : RowBandReceipt 15 3 4 :=
  rowTileFull_to_rowBand 15 3 receipt_row_15_y03_full

private theorem receipt_row_15_fast : FastRowReceipt 15 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_15_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_15_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_15_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_15_band_03_04 cy (by omega) h_4
  by_cases h_6 : cy.val < 6
  · exact receipt_row_15_band_04_06 cy (by omega) h_6
  by_cases h_8 : cy.val < 8
  · exact receipt_row_15_band_06_08 cy (by omega) h_8
  by_cases h_10 : cy.val < 10
  · exact receipt_row_15_band_08_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_15_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_15_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_15_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_15_band_16_18 cy (by omega) h_18
  · exact receipt_row_15_band_18_23 cy (by omega) (by omega)

theorem receipt_row_15 : RowReceipt 15 :=
  fastRowReceipt_to_rowReceipt 15 receipt_row_15_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
