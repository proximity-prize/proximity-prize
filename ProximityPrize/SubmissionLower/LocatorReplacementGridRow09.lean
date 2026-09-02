import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09B00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Y02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Y03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09Y04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09B05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09B09
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09B13
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09B17
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09B21

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem receipt_row_09_fast : FastRowReceipt 9 := by
  intro cy
  by_cases hb0 : cy.val < 2
  · exact receipt_row_09_b00 cy (by omega) hb0
  by_cases hb1 : cy.val < 3
  · exact receipt_row_09_band_y02 cy (by omega) hb1
  by_cases hb2 : cy.val < 4
  · exact receipt_row_09_band_y03 cy (by omega) hb2
  by_cases hb3 : cy.val < 5
  · exact receipt_row_09_band_y04 cy (by omega) hb3
  by_cases hb4 : cy.val < 9
  · exact receipt_row_09_b05 cy (by omega) hb4
  by_cases hb5 : cy.val < 13
  · exact receipt_row_09_b09 cy (by omega) hb5
  by_cases hb6 : cy.val < 17
  · exact receipt_row_09_b13 cy (by omega) hb6
  by_cases hb7 : cy.val < 21
  · exact receipt_row_09_b17 cy (by omega) hb7
  · exact receipt_row_09_b21 cy (by omega) (by omega)

theorem receipt_row_09 : RowReceipt 9 :=
  fastRowReceipt_to_rowReceipt 9 receipt_row_09_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
