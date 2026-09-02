import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03_y00_full : RowTileReceipt 3 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_00_01 : RowBandReceipt 3 0 1 :=
  rowTileFull_to_rowBand 3 0 receipt_row_03_y00_full

theorem receipt_row_03_y01_full : RowTileReceipt 3 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_01_02 : RowBandReceipt 3 1 2 :=
  rowTileFull_to_rowBand 3 1 receipt_row_03_y01_full

theorem receipt_row_03_y02_full : RowTileReceipt 3 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y02_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_02_03 : RowBandReceipt 3 2 3 :=
  rowTileFull_to_rowBand 3 2 receipt_row_03_y02_full

theorem receipt_row_03_y03_full : RowTileReceipt 3 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y03_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y03_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_03_04 : RowBandReceipt 3 3 4 :=
  rowTileFull_to_rowBand 3 3 receipt_row_03_y03_full

theorem receipt_row_03_y04_full : RowTileReceipt 3 4 5 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y04_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y04_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_04_05 : RowBandReceipt 3 4 5 :=
  rowTileFull_to_rowBand 3 4 receipt_row_03_y04_full

theorem receipt_row_03_y05_full : RowTileReceipt 3 5 6 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y05_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y05_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_05_06 : RowBandReceipt 3 5 6 :=
  rowTileFull_to_rowBand 3 5 receipt_row_03_y05_full

theorem receipt_row_03_y06_full : RowTileReceipt 3 6 7 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_03_y06_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y06_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_06_07 : RowBandReceipt 3 6 7 :=
  rowTileFull_to_rowBand 3 6 receipt_row_03_y06_full

theorem receipt_row_03_y07_full : RowTileReceipt 3 7 8 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  · exact receipt_row_03_y07_t00_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_07_08 : RowBandReceipt 3 7 8 :=
  rowTileFull_to_rowBand 3 7 receipt_row_03_y07_full

theorem receipt_row_03_y08_full : RowTileReceipt 3 8 9 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  · exact receipt_row_03_y08_t00_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_08_09 : RowBandReceipt 3 8 9 :=
  rowTileFull_to_rowBand 3 8 receipt_row_03_y08_full

theorem receipt_row_03_y09_full : RowTileReceipt 3 9 10 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 12
  · exact receipt_row_03_y09_t00_12 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y09_t12_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_09_10 : RowBandReceipt 3 9 10 :=
  rowTileFull_to_rowBand 3 9 receipt_row_03_y09_full

theorem receipt_row_03_y10_full : RowTileReceipt 3 10 11 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 12
  · exact receipt_row_03_y10_t00_12 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y10_t12_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_10_11 : RowBandReceipt 3 10 11 :=
  rowTileFull_to_rowBand 3 10 receipt_row_03_y10_full

private theorem receipt_row_03_fast : FastRowReceipt 3 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_03_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_03_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_03_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_03_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_03_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_03_band_05_06 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_03_band_06_07 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_03_band_07_08 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_03_band_08_09 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_03_band_09_10 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_03_band_10_11 cy (by omega) h_11
  by_cases h_13 : cy.val < 13
  · exact receipt_row_03_band_11_13 cy (by omega) h_13
  by_cases h_15 : cy.val < 15
  · exact receipt_row_03_band_13_15 cy (by omega) h_15
  by_cases h_17 : cy.val < 17
  · exact receipt_row_03_band_15_17 cy (by omega) h_17
  by_cases h_19 : cy.val < 19
  · exact receipt_row_03_band_17_19 cy (by omega) h_19
  by_cases h_21 : cy.val < 21
  · exact receipt_row_03_band_19_21 cy (by omega) h_21
  · exact receipt_row_03_band_21_23 cy (by omega) (by omega)

theorem receipt_row_03 : RowReceipt 3 :=
  fastRowReceipt_to_rowReceipt 3 receipt_row_03_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
