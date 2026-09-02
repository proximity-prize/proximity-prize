import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08B00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Y03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Y04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Y05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08Y06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08B07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08B11
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08B15
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08B19
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08B23

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem receipt_row_08_fast : FastRowReceipt 8 := by
  intro cy
  by_cases hb0 : cy.val < 3
  · exact receipt_row_08_b00 cy (by omega) hb0
  by_cases hb1 : cy.val < 4
  · exact receipt_row_08_band_y03 cy (by omega) hb1
  by_cases hb2 : cy.val < 5
  · exact receipt_row_08_band_y04 cy (by omega) hb2
  by_cases hb3 : cy.val < 6
  · exact receipt_row_08_band_y05 cy (by omega) hb3
  by_cases hb4 : cy.val < 7
  · exact receipt_row_08_band_y06 cy (by omega) hb4
  by_cases hb5 : cy.val < 11
  · exact receipt_row_08_b07 cy (by omega) hb5
  by_cases hb6 : cy.val < 15
  · exact receipt_row_08_b11 cy (by omega) hb6
  by_cases hb7 : cy.val < 19
  · exact receipt_row_08_b15 cy (by omega) hb7
  by_cases hb8 : cy.val < 23
  · exact receipt_row_08_b19 cy (by omega) hb8
  · exact receipt_row_08_b23 cy (by omega) (by omega)

theorem receipt_row_08 : RowReceipt 8 :=
  fastRowReceipt_to_rowReceipt 8 receipt_row_08_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
