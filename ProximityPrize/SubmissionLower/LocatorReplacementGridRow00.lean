import ProximityPrize.SubmissionLower.LocatorReplacementGridRow00S00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_00_y00_full : RowTileReceipt 0 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_00_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_00_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_00_band_00_01 : RowBandReceipt 0 0 1 :=
  rowTileFull_to_rowBand 0 0 receipt_row_00_y00_full

private theorem receipt_row_00_fast : FastRowReceipt 0 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_00_band_00_01 cy (by omega) h_1
  by_cases h_3 : cy.val < 3
  · exact receipt_row_00_band_01_03 cy (by omega) h_3
  by_cases h_5 : cy.val < 5
  · exact receipt_row_00_band_03_05 cy (by omega) h_5
  by_cases h_7 : cy.val < 7
  · exact receipt_row_00_band_05_07 cy (by omega) h_7
  by_cases h_9 : cy.val < 9
  · exact receipt_row_00_band_07_09 cy (by omega) h_9
  by_cases h_11 : cy.val < 11
  · exact receipt_row_00_band_09_11 cy (by omega) h_11
  by_cases h_13 : cy.val < 13
  · exact receipt_row_00_band_11_13 cy (by omega) h_13
  by_cases h_15 : cy.val < 15
  · exact receipt_row_00_band_13_15 cy (by omega) h_15
  by_cases h_17 : cy.val < 17
  · exact receipt_row_00_band_15_17 cy (by omega) h_17
  by_cases h_19 : cy.val < 19
  · exact receipt_row_00_band_17_19 cy (by omega) h_19
  by_cases h_21 : cy.val < 21
  · exact receipt_row_00_band_19_21 cy (by omega) h_21
  · exact receipt_row_00_band_21_23 cy (by omega) (by omega)

theorem receipt_row_00 : RowReceipt 0 :=
  fastRowReceipt_to_rowReceipt 0 receipt_row_00_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
