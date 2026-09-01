import ProximityPrize.SubmissionLower.LocatorReplacementGridRow15

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_17_band_00 : RowBandReceipt 17 0 3 := by decide +kernel

theorem receipt_row_17_band_01 : RowBandReceipt 17 3 4 := by decide +kernel

theorem receipt_row_17_band_02 : RowBandReceipt 17 4 5 := by decide +kernel

theorem receipt_row_17_band_03 : RowBandReceipt 17 5 6 := by decide +kernel

theorem receipt_row_17_band_04 : RowBandReceipt 17 6 7 := by decide +kernel

theorem receipt_row_17_band_05 : RowBandReceipt 17 7 8 := by decide +kernel

theorem receipt_row_17_band_06 : RowBandReceipt 17 8 9 := by decide +kernel

theorem receipt_row_17_band_07 : RowBandReceipt 17 9 10 := by decide +kernel

theorem receipt_row_17_band_08 : RowBandReceipt 17 10 11 := by decide +kernel

theorem receipt_row_17_band_09 : RowBandReceipt 17 11 12 := by decide +kernel

theorem receipt_row_17_band_10 : RowBandReceipt 17 12 13 := by decide +kernel

theorem receipt_row_17_band_11 : RowBandReceipt 17 13 14 := by decide +kernel

theorem receipt_row_17_band_12 : RowBandReceipt 17 14 21 := by decide +kernel

theorem receipt_row_17 : RowReceipt 17 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_17_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_17_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_17_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_17_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_17_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_17_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_17_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_17_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_17_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_17_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_17_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_17_band_11 cy (by omega) h_14
  · exact receipt_row_17_band_12 cy (by omega) (by omega)

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
