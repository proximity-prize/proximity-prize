import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09S07

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_09_y00_full : RowTileReceipt 9 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_09_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_09_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_00_01 : RowBandReceipt 9 0 1 :=
  rowTileFull_to_rowBand 9 0 receipt_row_09_y00_full

theorem receipt_row_09_y01_full : RowTileReceipt 9 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_09_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_09_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_01_02 : RowBandReceipt 9 1 2 :=
  rowTileFull_to_rowBand 9 1 receipt_row_09_y01_full

theorem receipt_row_09_y02_full : RowTileReceipt 9 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 8
  · exact receipt_row_09_y02_t00_08 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_09_y02_t08_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_02_03 : RowBandReceipt 9 2 3 :=
  rowTileFull_to_rowBand 9 2 receipt_row_09_y02_full

theorem receipt_row_09_y03_full : RowTileReceipt 9 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_09_y03_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 9
  · exact receipt_row_09_y03_t01_09 cy hylo hyhi ct (by omega) h1
  · exact receipt_row_09_y03_t09_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_03_04 : RowBandReceipt 9 3 4 :=
  rowTileFull_to_rowBand 9 3 receipt_row_09_y03_full

theorem receipt_row_09_y04_full : RowTileReceipt 9 4 5 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 1
  · exact receipt_row_09_y04_t00_01 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 3
  · exact receipt_row_09_y04_t01_03 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 5
  · exact receipt_row_09_y04_t03_05 cy hylo hyhi ct (by omega) h2
  · exact receipt_row_09_y04_t05_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_09_band_04_05 : RowBandReceipt 9 4 5 :=
  rowTileFull_to_rowBand 9 4 receipt_row_09_y04_full

private theorem receipt_row_09_fast : FastRowReceipt 9 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_09_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_09_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_09_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_09_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_09_band_04_05 cy (by omega) h_5
  by_cases h_7 : cy.val < 7
  · exact receipt_row_09_band_05_07 cy (by omega) h_7
  by_cases h_9 : cy.val < 9
  · exact receipt_row_09_band_07_09 cy (by omega) h_9
  by_cases h_11 : cy.val < 11
  · exact receipt_row_09_band_09_11 cy (by omega) h_11
  by_cases h_13 : cy.val < 13
  · exact receipt_row_09_band_11_13 cy (by omega) h_13
  by_cases h_15 : cy.val < 15
  · exact receipt_row_09_band_13_15 cy (by omega) h_15
  by_cases h_17 : cy.val < 17
  · exact receipt_row_09_band_15_17 cy (by omega) h_17
  by_cases h_19 : cy.val < 19
  · exact receipt_row_09_band_17_19 cy (by omega) h_19
  · exact receipt_row_09_band_19_23 cy (by omega) (by omega)

theorem receipt_row_09 : RowReceipt 9 :=
  fastRowReceipt_to_rowReceipt 9 receipt_row_09_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
