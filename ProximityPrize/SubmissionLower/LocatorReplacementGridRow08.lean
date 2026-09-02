import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S08
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08S09

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_08_y00_full : RowTileReceipt 8 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_08_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_00_01 : RowBandReceipt 8 0 1 :=
  rowTileFull_to_rowBand 8 0 receipt_row_08_y00_full

theorem receipt_row_08_y01_full : RowTileReceipt 8 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_08_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_01_02 : RowBandReceipt 8 1 2 :=
  rowTileFull_to_rowBand 8 1 receipt_row_08_y01_full

theorem receipt_row_08_y02_full : RowTileReceipt 8 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_08_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y02_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_02_03 : RowBandReceipt 8 2 3 :=
  rowTileFull_to_rowBand 8 2 receipt_row_08_y02_full

theorem receipt_row_08_y03_full : RowTileReceipt 8 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_08_y03_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_08_y03_t08_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_03_04 : RowBandReceipt 8 3 4 :=
  rowTileFull_to_rowBand 8 3 receipt_row_08_y03_full

theorem receipt_row_08_y04_full : RowTileReceipt 8 4 5 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_08_y04_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 9
  · exact receipt_row_08_y04_t01_09 cy hylo hyhi ct (by omega) h1
  · exact receipt_row_08_y04_t09_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_04_05 : RowBandReceipt 8 4 5 :=
  rowTileFull_to_rowBand 8 4 receipt_row_08_y04_full

theorem receipt_row_08_y05_full : RowTileReceipt 8 5 6 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_08_y05_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 3
  · exact receipt_row_08_y05_t01_03 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 5
  · exact receipt_row_08_y05_t03_05 cy hylo hyhi ct (by omega) h2
  by_cases h3 : ct.val < 7
  · exact receipt_row_08_y05_t05_07 cy hylo hyhi ct (by omega) h3
  · exact receipt_row_08_y05_t07_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_05_06 : RowBandReceipt 8 5 6 :=
  rowTileFull_to_rowBand 8 5 receipt_row_08_y05_full

theorem receipt_row_08_y06_full : RowTileReceipt 8 6 7 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_08_y06_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 2
  · exact receipt_row_08_y06_t01_02 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 4
  · exact receipt_row_08_y06_t02_04 cy hylo hyhi ct (by omega) h2
  by_cases h3 : ct.val < 6
  · exact receipt_row_08_y06_t04_06 cy hylo hyhi ct (by omega) h3
  · exact receipt_row_08_y06_t06_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_08_band_06_07 : RowBandReceipt 8 6 7 :=
  rowTileFull_to_rowBand 8 6 receipt_row_08_y06_full

private theorem receipt_row_08_fast : FastRowReceipt 8 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_08_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_08_band_01_02 cy (by omega) h_2
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
  · exact receipt_row_08_band_19_23 cy (by omega) (by omega)

theorem receipt_row_08 : RowReceipt 8 :=
  fastRowReceipt_to_rowReceipt 8 receipt_row_08_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
