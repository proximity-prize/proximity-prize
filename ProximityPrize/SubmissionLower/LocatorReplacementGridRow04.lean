import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04S08

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_04_y00_full : RowTileReceipt 4 0 1 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_04_y00_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y00_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_00_01 : RowBandReceipt 4 0 1 :=
  rowTileFull_to_rowBand 4 0 receipt_row_04_y00_full

theorem receipt_row_04_y01_full : RowTileReceipt 4 1 2 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_04_y01_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y01_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_01_02 : RowBandReceipt 4 1 2 :=
  rowTileFull_to_rowBand 4 1 receipt_row_04_y01_full

theorem receipt_row_04_y02_full : RowTileReceipt 4 2 3 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_04_y02_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y02_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_02_03 : RowBandReceipt 4 2 3 :=
  rowTileFull_to_rowBand 4 2 receipt_row_04_y02_full

theorem receipt_row_04_y03_full : RowTileReceipt 4 3 4 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_04_y03_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y03_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_03_04 : RowBandReceipt 4 3 4 :=
  rowTileFull_to_rowBand 4 3 receipt_row_04_y03_full

theorem receipt_row_04_y04_full : RowTileReceipt 4 4 5 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_04_y04_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y04_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_04_05 : RowBandReceipt 4 4 5 :=
  rowTileFull_to_rowBand 4 4 receipt_row_04_y04_full

theorem receipt_row_04_y05_full : RowTileReceipt 4 5 6 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 24
  · exact receipt_row_04_y05_t00_24 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y05_t24_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_05_06 : RowBandReceipt 4 5 6 :=
  rowTileFull_to_rowBand 4 5 receipt_row_04_y05_full

theorem receipt_row_04_y06_full : RowTileReceipt 4 6 7 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 25
  · exact receipt_row_04_y06_t00_25 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y06_t25_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_06_07 : RowBandReceipt 4 6 7 :=
  rowTileFull_to_rowBand 4 6 receipt_row_04_y06_full

theorem receipt_row_04_y07_full : RowTileReceipt 4 7 8 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 12
  · exact receipt_row_04_y07_t00_12 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y07_t12_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_07_08 : RowBandReceipt 4 7 8 :=
  rowTileFull_to_rowBand 4 7 receipt_row_04_y07_full

theorem receipt_row_04_y08_full : RowTileReceipt 4 8 9 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 12
  · exact receipt_row_04_y08_t00_12 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y08_t12_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_08_09 : RowBandReceipt 4 8 9 :=
  rowTileFull_to_rowBand 4 8 receipt_row_04_y08_full

theorem receipt_row_04_y09_full : RowTileReceipt 4 9 10 0 26 := by
  intro cy hylo hyhi ct htlo hthi
  by_cases h0 : ct.val < 2
  · exact receipt_row_04_y09_t00_02 cy hylo hyhi ct (by omega) h0
  · exact receipt_row_04_y09_t02_26 cy hylo hyhi ct (by omega) hthi

theorem receipt_row_04_band_09_10 : RowBandReceipt 4 9 10 :=
  rowTileFull_to_rowBand 4 9 receipt_row_04_y09_full

private theorem receipt_row_04_fast : FastRowReceipt 4 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_04_band_00_01 cy (by omega) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_04_band_01_02 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_04_band_02_03 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_04_band_03_04 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_04_band_04_05 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_04_band_05_06 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_04_band_06_07 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_04_band_07_08 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_04_band_08_09 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_04_band_09_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_04_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_04_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_04_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_04_band_16_18 cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_04_band_18_20 cy (by omega) h_20
  · exact receipt_row_04_band_20_23 cy (by omega) (by omega)

theorem receipt_row_04 : RowReceipt 4 :=
  fastRowReceipt_to_rowReceipt 4 receipt_row_04_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
