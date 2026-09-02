import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Hot06B

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_08_fast : FastRowReceipt 8 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_08_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_08_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_08_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_08_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_08_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_08_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_08_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_08_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_08_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_08_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_08_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_08_band_11 cy (by omega) h_14
  · exact receipt_row_08_band_12 cy (by omega) (by omega)

theorem receipt_row_08 : RowReceipt 8 :=
  fastRowReceipt_to_rowReceipt 8 receipt_row_08_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
