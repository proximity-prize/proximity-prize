import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05S00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_y03_full : RowTileReceipt 5 3 4 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_05_y03_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_05_y03_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_03_04 : RowBandReceipt 5 3 4 :=
  rowTileFull_to_rowBand 5 3 receipt_row_05_y03_full

theorem receipt_row_05_y04_full : RowTileReceipt 5 4 5 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_05_y04_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_05_y04_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_04_05 : RowBandReceipt 5 4 5 :=
  rowTileFull_to_rowBand 5 4 receipt_row_05_y04_full

theorem receipt_row_05_y05_full : RowTileReceipt 5 5 6 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_05_y05_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_05_y05_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_05_06 : RowBandReceipt 5 5 6 :=
  rowTileFull_to_rowBand 5 5 receipt_row_05_y05_full

theorem receipt_row_05_y06_full : RowTileReceipt 5 6 7 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 10
  · exact receipt_row_05_y06_t00_10 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_05_y06_t10_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_06_07 : RowBandReceipt 5 6 7 :=
  rowTileFull_to_rowBand 5 6 receipt_row_05_y06_full

theorem receipt_row_05_y07_full : RowTileReceipt 5 7 8 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_05_y07_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 26
  · exact receipt_row_05_y07_t02_26 cy hylo hyhi ct (by omega) h1
  · exact receipt_row_05_y07_t26_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_07_08 : RowBandReceipt 5 7 8 :=
  rowTileFull_to_rowBand 5 7 receipt_row_05_y07_full

theorem receipt_row_05_y08_full : RowTileReceipt 5 8 9 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_05_y08_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 4
  · exact receipt_row_05_y08_t02_04 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 12
  · exact receipt_row_05_y08_t04_12 cy hylo hyhi ct (by omega) h2
  · exact receipt_row_05_y08_t12_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_08_09 : RowBandReceipt 5 8 9 :=
  rowTileFull_to_rowBand 5 8 receipt_row_05_y08_full

theorem receipt_row_05_y09_full : RowTileReceipt 5 9 10 0 30 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 28
  · exact receipt_row_05_y09_t00_28 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_05_y09_t28_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_05_band_09_10 : RowBandReceipt 5 9 10 :=
  rowTileFull_to_rowBand 5 9 receipt_row_05_y09_full

private theorem receipt_row_05_fast : FastRowReceipt 5 := by
  intro cy
  by_cases h_2 : cy.val < 2
  · exact receipt_row_05_band_00_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_05_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_05_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_05_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_05_band_05_06 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_05_band_06_07 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_05_band_07_08 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_05_band_08_09 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_05_band_09_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_05_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_05_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_05_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_05_band_16_18 cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_05_band_18_20 cy (by omega) h_20
  by_cases h_22 : cy.val < 22
  · exact receipt_row_05_band_20_22 cy (by omega) h_22
  · exact receipt_row_05_band_22_25 cy (by omega) cy.isLt

theorem receipt_row_05 : RowReceipt 5 :=
  fastRowReceipt_to_rowReceipt 5 receipt_row_05_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
