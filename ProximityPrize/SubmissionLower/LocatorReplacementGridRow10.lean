import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10S00

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_10_y02_full : RowTileReceipt 10 2 3 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_10_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_10_y02_t24_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_10_band_02_03 : RowBandReceipt 10 2 3 :=
  rowTileFull_to_rowBand 10 2 receipt_row_10_y02_full

theorem receipt_row_10_y03_full : RowTileReceipt 10 3 4 0 29 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_10_y03_t00_02 cy hylo hyhi ct (by omega) h0
  by_cases h1 : ct.val < 4
  · exact receipt_row_10_y03_t02_04 cy hylo hyhi ct (by omega) h1
  by_cases h2 : ct.val < 28
  · exact receipt_row_10_y03_t04_28 cy hylo hyhi ct (by omega) h2
  · exact receipt_row_10_y03_t28_29 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_10_band_03_04 : RowBandReceipt 10 3 4 :=
  rowTileFull_to_rowBand 10 3 receipt_row_10_y03_full

private theorem receipt_row_10_fast : FastRowReceipt 10 := by
  intro cy
  by_cases h_2 : cy.val < 2
  · exact receipt_row_10_band_00_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_10_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_10_band_03_04 cy (by omega) h_4
  by_cases h_6 : cy.val < 6
  · exact receipt_row_10_band_04_06 cy (by omega) h_6
  by_cases h_8 : cy.val < 8
  · exact receipt_row_10_band_06_08 cy (by omega) h_8
  by_cases h_10 : cy.val < 10
  · exact receipt_row_10_band_08_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_10_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_10_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_10_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_10_band_16_18 cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_10_band_18_20 cy (by omega) h_20
  by_cases h_22 : cy.val < 22
  · exact receipt_row_10_band_20_22 cy (by omega) h_22
  · exact receipt_row_10_band_22_25 cy (by omega) cy.isLt

theorem receipt_row_10 : RowReceipt 10 :=
  fastRowReceipt_to_rowReceipt 10 receipt_row_10_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
