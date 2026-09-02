import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000




theorem receipt_row_12_band_00_02 : RowBandReceipt 12 0 2 := by decide +kernel

theorem receipt_row_12_band_02_04 : RowBandReceipt 12 2 4 := by decide +kernel





theorem receipt_row_12_band_04_06 : RowBandReceipt 12 4 6 := by decide +kernel

theorem receipt_row_12_band_06_08 : RowBandReceipt 12 6 8 := by decide +kernel





theorem receipt_row_12_band_08_10 : RowBandReceipt 12 8 10 := by decide +kernel

theorem receipt_row_12_band_10_12 : RowBandReceipt 12 10 12 := by decide +kernel





theorem receipt_row_12_band_12_14 : RowBandReceipt 12 12 14 := by decide +kernel

theorem receipt_row_12_band_14_16 : RowBandReceipt 12 14 16 := by decide +kernel





theorem receipt_row_12_band_16_18 : RowBandReceipt 12 16 18 := by decide +kernel

theorem receipt_row_12_band_18_23 : RowBandReceipt 12 18 23 := by decide +kernel





private theorem receipt_row_12_fast : FastRowReceipt 12 := by
  intro cy
  by_cases h_2 : cy.val < 2
  · exact receipt_row_12_band_00_02 cy (by omega) h_2
  by_cases h_4 : cy.val < 4
  · exact receipt_row_12_band_02_04 cy (by omega) h_4
  by_cases h_6 : cy.val < 6
  · exact receipt_row_12_band_04_06 cy (by omega) h_6
  by_cases h_8 : cy.val < 8
  · exact receipt_row_12_band_06_08 cy (by omega) h_8
  by_cases h_10 : cy.val < 10
  · exact receipt_row_12_band_08_10 cy (by omega) h_10
  by_cases h_12 : cy.val < 12
  · exact receipt_row_12_band_10_12 cy (by omega) h_12
  by_cases h_14 : cy.val < 14
  · exact receipt_row_12_band_12_14 cy (by omega) h_14
  by_cases h_16 : cy.val < 16
  · exact receipt_row_12_band_14_16 cy (by omega) h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_12_band_16_18 cy (by omega) h_18
  · exact receipt_row_12_band_18_23 cy (by omega) (by omega)

theorem receipt_row_12 : RowReceipt 12 :=
  fastRowReceipt_to_rowReceipt 12 receipt_row_12_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
