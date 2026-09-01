import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot08B
import ProximityPrize.SubmissionLower.LocatorReplacementGridY22

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_07_fast : FastRowReceipt 7 := by
  intro cy
  by_cases h₀ : cy.val < 3
  · exact receipt_row_07_band_00 cy (Nat.zero_le _) h₀
  by_cases h_4 : cy.val < 4
  · exact receipt_row_07_band_01 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_07_band_02 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_07_band_03 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_07_band_04 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_07_band_05 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_07_band_06 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_07_band_07 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_07_band_08 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_07_band_09 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_07_band_10 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_07_band_11 cy (by omega) h_14
  by_cases h_15 : cy.val < 22
  · exact receipt_row_07_band_12 cy (by omega) h_15
  · exact receipt_y_22 7 cy (by omega) (by simpa [coarseYCells, ysCap] using cy.isLt)

theorem receipt_row_07 : RowReceipt 7 :=
  fastRowReceipt_to_rowReceipt 7 receipt_row_07_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
