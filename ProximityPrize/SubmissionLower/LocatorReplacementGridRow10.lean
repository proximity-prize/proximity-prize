import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S05

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

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
