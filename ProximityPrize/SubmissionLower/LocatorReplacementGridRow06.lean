import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S08
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S09
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S10
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06S11

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_06_y00_full : RowTileReceipt 6 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_06_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_06_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_00_01 : RowBandReceipt 6 0 1 :=
  rowTileFull_to_rowBand 6 0 receipt_row_06_y00_full

theorem receipt_row_06_y01_full : RowTileReceipt 6 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_06_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_06_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_01_02 : RowBandReceipt 6 1 2 :=
  rowTileFull_to_rowBand 6 1 receipt_row_06_y01_full

theorem receipt_row_06_y02_full : RowTileReceipt 6 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_06_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_06_y02_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_02_03 : RowBandReceipt 6 2 3 :=
  rowTileFull_to_rowBand 6 2 receipt_row_06_y02_full

theorem receipt_row_06_y03_full : RowTileReceipt 6 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_06_y03_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_06_y03_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_03_04 : RowBandReceipt 6 3 4 :=
  rowTileFull_to_rowBand 6 3 receipt_row_06_y03_full

theorem receipt_row_06_y04_full : RowTileReceipt 6 4 5 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_06_y04_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_06_y04_t08_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_04_05 : RowBandReceipt 6 4 5 :=
  rowTileFull_to_rowBand 6 4 receipt_row_06_y04_full

theorem receipt_row_06_y05_full : RowTileReceipt 6 5 6 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_06_y05_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_06_y05_t08_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_05_06 : RowBandReceipt 6 5 6 :=
  rowTileFull_to_rowBand 6 5 receipt_row_06_y05_full

theorem receipt_row_06_y06_full : RowTileReceipt 6 6 7 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_06_y06_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 9
  · exact receipt_row_06_y06_t01_09 cy hylo hyhi ct (by omega) h1
  · exact receipt_row_06_y06_t09_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_06_07 : RowBandReceipt 6 6 7 :=
  rowTileFull_to_rowBand 6 6 receipt_row_06_y06_full

theorem receipt_row_06_y07_full : RowTileReceipt 6 7 8 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_06_y07_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 4
  · exact receipt_row_06_y07_t02_04 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 12
  · exact receipt_row_06_y07_t04_12 cy hylo hyhi ct (by omega) h2
  · exact receipt_row_06_y07_t12_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_07_08 : RowBandReceipt 6 7 8 :=
  rowTileFull_to_rowBand 6 7 receipt_row_06_y07_full

theorem receipt_row_06_y08_full : RowTileReceipt 6 8 9 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_06_y08_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 3
  · exact receipt_row_06_y08_t01_03 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 5
  · exact receipt_row_06_y08_t03_05 cy hylo hyhi ct (by omega) h2
  by_cases h3 : ct.val < 7
  · exact receipt_row_06_y08_t05_07 cy hylo hyhi ct (by omega) h3
  by_cases h4 : ct.val < 9
  · exact receipt_row_06_y08_t07_09 cy hylo hyhi ct (by omega) h4
  by_cases h5 : ct.val < 11
  · exact receipt_row_06_y08_t09_11 cy hylo hyhi ct (by omega) h5
  by_cases h6 : ct.val < 13
  · exact receipt_row_06_y08_t11_13 cy hylo hyhi ct (by omega) h6
  by_cases h7 : ct.val < 21
  · exact receipt_row_06_y08_t13_21 cy hylo hyhi ct (by omega) h7
  · exact receipt_row_06_y08_t21_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_06_band_08_09 : RowBandReceipt 6 8 9 :=
  rowTileFull_to_rowBand 6 8 receipt_row_06_y08_full

private theorem receipt_row_06_fast : FastRowReceipt 6 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_06_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_06_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_06_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_06_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_06_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_06_band_05_06 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_06_band_06_07 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_06_band_07_08 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_06_band_08_09 cy (by omega) h_9
  by_cases h_11 : cy.val < 11
  · exact receipt_row_06_band_09_11 cy (by omega) h_11
  by_cases h_13 : cy.val < 13
  · exact receipt_row_06_band_11_13 cy (by omega) h_13
  by_cases h_15 : cy.val < 15
  · exact receipt_row_06_band_13_15 cy (by omega) h_15
  by_cases h_17 : cy.val < 17
  · exact receipt_row_06_band_15_17 cy (by omega) h_17
  by_cases h_19 : cy.val < 19
  · exact receipt_row_06_band_17_19 cy (by omega) h_19
  by_cases h_21 : cy.val < 21
  · exact receipt_row_06_band_19_21 cy (by omega) h_21
  · exact receipt_row_06_band_21_23 cy (by omega) (by omega)

theorem receipt_row_06 : RowReceipt 6 :=
  fastRowReceipt_to_rowReceipt 6 receipt_row_06_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
