import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_y02_full : RowTileReceipt 8 2 3 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_08_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y02_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_02_03 : RowBandReceipt 8 2 3 :=
  rowTileFull_to_rowBand 8 2 receipt_row_08_y02_full

theorem receipt_row_08_y03_full : RowTileReceipt 8 3 4 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_08_y03_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y03_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_03_04 : RowBandReceipt 8 3 4 :=
  rowTileFull_to_rowBand 8 3 receipt_row_08_y03_full

theorem receipt_row_08_y04_full : RowTileReceipt 8 4 5 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_08_y04_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 26
  · exact receipt_row_08_y04_t02_26 cy hylo hyhi ct (by omega) h1
  · exact receipt_row_08_y04_t26_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_04_05 : RowBandReceipt 8 4 5 :=
  rowTileFull_to_rowBand 8 4 receipt_row_08_y04_full

theorem receipt_row_08_y05_full : RowTileReceipt 8 5 6 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_08_y05_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 4
  · exact receipt_row_08_y05_t02_04 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 6
  · exact receipt_row_08_y05_t04_06 cy hylo hyhi ct (by omega) h2
  by_cases h3 : ct.val < 8
  · exact receipt_row_08_y05_t06_08 cy hylo hyhi ct (by omega) h3
  by_cases h4 : ct.val < 10
  · exact receipt_row_08_y05_t08_10 cy hylo hyhi ct (by omega) h4
  by_cases h5 : ct.val < 12
  · exact receipt_row_08_y05_t10_12 cy hylo hyhi ct (by omega) h5
  by_cases h6 : ct.val < 20
  · exact receipt_row_08_y05_t12_20 cy hylo hyhi ct (by omega) h6
  · exact receipt_row_08_y05_t20_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_05_06 : RowBandReceipt 8 5 6 :=
  rowTileFull_to_rowBand 8 5 receipt_row_08_y05_full

theorem receipt_row_08_y06_full : RowTileReceipt 8 6 7 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 28
  · exact receipt_row_08_y06_t00_28 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y06_t28_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_06_07 : RowBandReceipt 8 6 7 :=
  rowTileFull_to_rowBand 8 6 receipt_row_08_y06_full

private theorem receipt_row_08_fast : FastRowReceipt 8 := by
  intro cy
  by_cases h_2 : cy.val < 2
  · exact receipt_row_08_band_00_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_08_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_08_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_08_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_08_band_05_06 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_08_band_06_07 cy (by omega) h_7
  by_cases h_9 : cy.val < 9
  · exact receipt_row_08_band_07_09 cy (by omega) h_9
  by_cases h_11 : cy.val < 11
  · exact receipt_row_08_band_09_11 cy (by omega) h_11
  by_cases h_13 : cy.val < 13
  · exact receipt_row_08_band_11_13 cy (by omega) h_13
  by_cases h_15 : cy.val < 15
  · exact receipt_row_08_band_13_15 cy (by omega) h_15
  by_cases h_17 : cy.val < 17
  · exact receipt_row_08_band_15_17 cy (by omega) h_17
  by_cases h_19 : cy.val < 19
  · exact receipt_row_08_band_17_19 cy (by omega) h_19
  by_cases h_21 : cy.val < 21
  · exact receipt_row_08_band_19_21 cy (by omega) h_21
  · exact receipt_row_08_band_21_25 cy (by omega) cy.isLt

theorem receipt_row_08 : RowReceipt 8 :=
  fastRowReceipt_to_rowReceipt 8 receipt_row_08_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
