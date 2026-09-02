import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03S00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03_y07_full : RowTileReceipt 3 7 8 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 28
  · exact receipt_row_03_y07_t00_28 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y07_t28_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_07_08 : RowBandReceipt 3 7 8 :=
  rowTileFull_to_rowBand 3 7 receipt_row_03_y07_full

theorem receipt_row_03_y08_full : RowTileReceipt 3 8 9 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 28
  · exact receipt_row_03_y08_t00_28 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y08_t28_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_08_09 : RowBandReceipt 3 8 9 :=
  rowTileFull_to_rowBand 3 8 receipt_row_03_y08_full

theorem receipt_row_03_y09_full : RowTileReceipt 3 9 10 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 28
  · exact receipt_row_03_y09_t00_28 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y09_t28_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_09_10 : RowBandReceipt 3 9 10 :=
  rowTileFull_to_rowBand 3 9 receipt_row_03_y09_full

theorem receipt_row_03_y10_full : RowTileReceipt 3 10 11 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 12
  · exact receipt_row_03_y10_t00_12 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_03_y10_t12_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_03_band_10_11 : RowBandReceipt 3 10 11 :=
  rowTileFull_to_rowBand 3 10 receipt_row_03_y10_full

private theorem receipt_row_03_fast : FastRowReceipt 3 := by
  intro cy
  by_cases h_2 : cy.val < 2
  · exact receipt_row_03_band_00_02 cy (by omega) h_2
  by_cases h_4 : cy.val < 4
  · exact receipt_row_03_band_02_04 cy (by omega) h_4
  by_cases h_6 : cy.val < 6
  · exact receipt_row_03_band_04_06 cy (by omega) h_6
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
  by_cases h_23 : cy.val < 23
  · exact receipt_row_03_band_21_23 cy (by omega) h_23
  · exact receipt_row_03_band_23_25 cy (by omega) cy.isLt

theorem receipt_row_03 : RowReceipt 3 :=
  fastRowReceipt_to_rowReceipt 3 receipt_row_03_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
