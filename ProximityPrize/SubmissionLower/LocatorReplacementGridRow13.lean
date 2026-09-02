import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13Seg10

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_row_13_fast : FastRowReceipt 13 := by
  intro cy
  by_cases h_1 : cy.val < 1
  · exact receipt_row_13_y_00 cy (Nat.zero_le _) h_1
  by_cases h_2 : cy.val < 2
  · exact receipt_row_13_y_01 cy (by omega) h_2
  by_cases h_3 : cy.val < 3
  · exact receipt_row_13_y_02 cy (by omega) h_3
  by_cases h_4 : cy.val < 4
  · exact receipt_row_13_y_03 cy (by omega) h_4
  by_cases h_5 : cy.val < 5
  · exact receipt_row_13_y_04 cy (by omega) h_5
  by_cases h_6 : cy.val < 6
  · exact receipt_row_13_y_05 cy (by omega) h_6
  by_cases h_7 : cy.val < 7
  · exact receipt_row_13_y_06 cy (by omega) h_7
  by_cases h_8 : cy.val < 8
  · exact receipt_row_13_y_07 cy (by omega) h_8
  by_cases h_9 : cy.val < 9
  · exact receipt_row_13_y_08 cy (by omega) h_9
  by_cases h_10 : cy.val < 10
  · exact receipt_row_13_y_09 cy (by omega) h_10
  by_cases h_11 : cy.val < 11
  · exact receipt_row_13_y_10 cy (by omega) h_11
  by_cases h_12 : cy.val < 12
  · exact receipt_row_13_y_11 cy (by omega) h_12
  by_cases h_13 : cy.val < 13
  · exact receipt_row_13_y_12 cy (by omega) h_13
  by_cases h_14 : cy.val < 14
  · exact receipt_row_13_y_13 cy (by omega) h_14
  by_cases h_15 : cy.val < 15
  · exact receipt_row_13_y_14 cy (by omega) h_15
  by_cases h_16 : cy.val < 16
  · exact receipt_row_13_y_15 cy (by omega) h_16
  by_cases h_17 : cy.val < 17
  · exact receipt_row_13_y_16 cy (by omega) h_17
  by_cases h_18 : cy.val < 18
  · exact receipt_row_13_y_17 cy (by omega) h_18
  by_cases h_19 : cy.val < 19
  · exact receipt_row_13_y_18 cy (by omega) h_19
  by_cases h_20 : cy.val < 20
  · exact receipt_row_13_y_19 cy (by omega) h_20
  by_cases h_21 : cy.val < 21
  · exact receipt_row_13_y_20 cy (by omega) h_21
  · exact receipt_row_13_y_21 cy (by omega) (by omega)

theorem receipt_row_13 : RowReceipt 13 :=
  fastRowReceipt_to_rowReceipt 13 receipt_row_13_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
