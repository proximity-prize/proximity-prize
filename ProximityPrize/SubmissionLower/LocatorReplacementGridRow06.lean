import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Y05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Y06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Y07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06Y08
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B09
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B13
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B17
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06B21

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem receipt_row_06_fast : FastRowReceipt 6 := by
  intro cy
  by_cases hb0 : cy.val < 4
  · exact receipt_row_06_b00 cy (by omega) hb0
  by_cases hb1 : cy.val < 5
  · exact receipt_row_06_b04 cy (by omega) hb1
  by_cases hb2 : cy.val < 6
  · exact receipt_row_06_band_y05 cy (by omega) hb2
  by_cases hb3 : cy.val < 7
  · exact receipt_row_06_band_y06 cy (by omega) hb3
  by_cases hb4 : cy.val < 8
  · exact receipt_row_06_band_y07 cy (by omega) hb4
  by_cases hb5 : cy.val < 9
  · exact receipt_row_06_band_y08 cy (by omega) hb5
  by_cases hb6 : cy.val < 13
  · exact receipt_row_06_b09 cy (by omega) hb6
  by_cases hb7 : cy.val < 17
  · exact receipt_row_06_b13 cy (by omega) hb7
  by_cases hb8 : cy.val < 21
  · exact receipt_row_06_b17 cy (by omega) hb8
  · exact receipt_row_06_b21 cy (by omega) (by omega)

theorem receipt_row_06 : RowReceipt 6 :=
  fastRowReceipt_to_rowReceipt 6 receipt_row_06_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
