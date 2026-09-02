import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05B00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05B04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Y07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Y08
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Y09
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05B10
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05B14
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05B18
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05B22

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem receipt_row_05_fast : FastRowReceipt 5 := by
  intro cy
  by_cases hb0 : cy.val < 4
  · exact receipt_row_05_b00 cy (by omega) hb0
  by_cases hb1 : cy.val < 7
  · exact receipt_row_05_b04 cy (by omega) hb1
  by_cases hb2 : cy.val < 8
  · exact receipt_row_05_band_y07 cy (by omega) hb2
  by_cases hb3 : cy.val < 9
  · exact receipt_row_05_band_y08 cy (by omega) hb3
  by_cases hb4 : cy.val < 10
  · exact receipt_row_05_band_y09 cy (by omega) hb4
  by_cases hb5 : cy.val < 14
  · exact receipt_row_05_b10 cy (by omega) hb5
  by_cases hb6 : cy.val < 18
  · exact receipt_row_05_b14 cy (by omega) hb6
  by_cases hb7 : cy.val < 22
  · exact receipt_row_05_b18 cy (by omega) hb7
  · exact receipt_row_05_b22 cy (by omega) (by omega)

theorem receipt_row_05 : RowReceipt 5 :=
  fastRowReceipt_to_rowReceipt 5 receipt_row_05_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
