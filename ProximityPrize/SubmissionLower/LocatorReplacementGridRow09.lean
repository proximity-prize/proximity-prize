import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_y02_full : RowTileReceipt 9 2 3 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_09_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_09_y02_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_02_03 : RowBandReceipt 9 2 3 :=
  rowTileFull_to_rowBand 9 2 receipt_row_09_y02_full

theorem receipt_row_09_y03_full : RowTileReceipt 9 3 4 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_09_y03_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_09_y03_t08_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_03_04 : RowBandReceipt 9 3 4 :=
  rowTileFull_to_rowBand 9 3 receipt_row_09_y03_full

theorem receipt_row_09_y04_full : RowTileReceipt 9 4 5 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_09_y04_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 4
  · exact receipt_row_09_y04_t02_04 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 6
  · exact receipt_row_09_y04_t04_06 cy hylo hyhi ct (by omega) h2
  · exact receipt_row_09_y04_t06_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_04_05 : RowBandReceipt 9 4 5 :=
  rowTileFull_to_rowBand 9 4 receipt_row_09_y04_full

theorem receipt_row_09_y05_full : RowTileReceipt 9 5 6 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 10
  · exact receipt_row_09_y05_t00_10 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_09_y05_t10_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_05_06 : RowBandReceipt 9 5 6 :=
  rowTileFull_to_rowBand 9 5 receipt_row_09_y05_full

private theorem receipt_row_09_fast : FastRowReceipt 9 := by
  intro cy
  by_cases h_2 : cy.val < 2
  · exact receipt_row_09_band_00_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_09_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_09_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_09_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_09_band_05_06 cy (by omega) h_6
  by_cases h_8 : cy.val < 8
  · exact receipt_row_09_band_06_08 cy (by omega) h_8
  by_cases h_10 : cy.val < 10
  · exact receipt_row_09_band_08_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_09_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_09_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_09_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_09_band_16_18 cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_09_band_18_20 cy (by omega) h_20
  by_cases h_22 : cy.val < 22
  · exact receipt_row_09_band_20_22 cy (by omega) h_22
  · exact receipt_row_09_band_22_25 cy (by omega) cy.isLt

theorem receipt_row_09 : RowReceipt 9 :=
  fastRowReceipt_to_rowReceipt 9 receipt_row_09_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
