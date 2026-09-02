import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07S01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_y00_full : RowTileReceipt 7 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_07_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_07_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_00_01 : RowBandReceipt 7 0 1 :=
  rowTileFull_to_rowBand 7 0 receipt_row_07_y00_full

theorem receipt_row_07_y01_full : RowTileReceipt 7 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_07_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_07_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_01_02 : RowBandReceipt 7 1 2 :=
  rowTileFull_to_rowBand 7 1 receipt_row_07_y01_full

theorem receipt_row_07_y02_full : RowTileReceipt 7 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_07_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_07_y02_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_02_03 : RowBandReceipt 7 2 3 :=
  rowTileFull_to_rowBand 7 2 receipt_row_07_y02_full

theorem receipt_row_07_y03_full : RowTileReceipt 7 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_07_y03_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_07_y03_t08_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_03_04 : RowBandReceipt 7 3 4 :=
  rowTileFull_to_rowBand 7 3 receipt_row_07_y03_full

theorem receipt_row_07_y04_full : RowTileReceipt 7 4 5 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 4
  · exact receipt_row_07_y04_t00_04 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_07_y04_t04_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_04_05 : RowBandReceipt 7 4 5 :=
  rowTileFull_to_rowBand 7 4 receipt_row_07_y04_full

theorem receipt_row_07_y05_full : RowTileReceipt 7 5 6 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_07_y05_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 3
  · exact receipt_row_07_y05_t01_03 cy hylo hyhi ct (by omega) h1
  · exact receipt_row_07_y05_t03_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_05_06 : RowBandReceipt 7 5 6 :=
  rowTileFull_to_rowBand 7 5 receipt_row_07_y05_full

theorem receipt_row_07_y06_full : RowTileReceipt 7 6 7 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_07_y06_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 2
  · exact receipt_row_07_y06_t01_02 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 4
  · exact receipt_row_07_y06_t02_04 cy hylo hyhi ct (by omega) h2
  by_cases h3 : ct.val < 6
  · exact receipt_row_07_y06_t04_06 cy hylo hyhi ct (by omega) h3
  by_cases h4 : ct.val < 8
  · exact receipt_row_07_y06_t06_08 cy hylo hyhi ct (by omega) h4
  by_cases h5 : ct.val < 10
  · exact receipt_row_07_y06_t08_10 cy hylo hyhi ct (by omega) h5
  by_cases h6 : ct.val < 18
  · exact receipt_row_07_y06_t10_18 cy hylo hyhi ct (by omega) h6
  · exact receipt_row_07_y06_t18_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_06_07 : RowBandReceipt 7 6 7 :=
  rowTileFull_to_rowBand 7 6 receipt_row_07_y06_full

theorem receipt_row_07_y07_full : RowTileReceipt 7 7 8 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_07_y07_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 2
  · exact receipt_row_07_y07_t01_02 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 3
  · exact receipt_row_07_y07_t02_03 cy hylo hyhi ct (by omega) h2
  by_cases h3 : ct.val < 4
  · exact receipt_row_07_y07_t03_04 cy hylo hyhi ct (by omega) h3
  by_cases h4 : ct.val < 5
  · exact receipt_row_07_y07_t04_05 cy hylo hyhi ct (by omega) h4
  by_cases h5 : ct.val < 6
  · exact receipt_row_07_y07_t05_06 cy hylo hyhi ct (by omega) h5
  by_cases h6 : ct.val < 7
  · exact receipt_row_07_y07_t06_07 cy hylo hyhi ct (by omega) h6
  by_cases h7 : ct.val < 8
  · exact receipt_row_07_y07_t07_08 cy hylo hyhi ct (by omega) h7
  by_cases h8 : ct.val < 9
  · exact receipt_row_07_y07_t08_09 cy hylo hyhi ct (by omega) h8
  by_cases h9 : ct.val < 10
  · exact receipt_row_07_y07_t09_10 cy hylo hyhi ct (by omega) h9
  by_cases h10 : ct.val < 11
  · exact receipt_row_07_y07_t10_11 cy hylo hyhi ct (by omega) h10
  by_cases h11 : ct.val < 13
  · exact receipt_row_07_y07_t11_13 cy hylo hyhi ct (by omega) h11
  by_cases h12 : ct.val < 15
  · exact receipt_row_07_y07_t13_15 cy hylo hyhi ct (by omega) h12
  by_cases h13 : ct.val < 17
  · exact receipt_row_07_y07_t15_17 cy hylo hyhi ct (by omega) h13
  by_cases h14 : ct.val < 25
  · exact receipt_row_07_y07_t17_25 cy hylo hyhi ct (by omega) h14
  · exact receipt_row_07_y07_t25_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_07_band_07_08 : RowBandReceipt 7 7 8 :=
  rowTileFull_to_rowBand 7 7 receipt_row_07_y07_full

private theorem receipt_row_07_fast : FastRowReceipt 7 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_07_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_07_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_07_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_07_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_07_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_07_band_05_06 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_07_band_06_07 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_07_band_07_08 cy (by omega) h_8
  by_cases h_10 : cy.val < 10
  · exact receipt_row_07_band_08_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_07_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_07_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_07_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_07_band_16_18 cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_07_band_18_20 cy (by omega) h_20
  · exact receipt_row_07_band_20_23 cy (by omega) (by omega)

theorem receipt_row_07 : RowReceipt 7 :=
  fastRowReceipt_to_rowReceipt 7 receipt_row_07_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
