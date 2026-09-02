import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07B00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Y04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Y05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Y06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Y07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07B08
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07B12
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07B16
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07B20

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem receipt_row_07_fast : FastRowReceipt 7 := by
  intro cy
  by_cases hb0 : cy.val < 4
  · exact receipt_row_07_b00 cy (by omega) hb0
  by_cases hb1 : cy.val < 5
  · exact receipt_row_07_band_y04 cy (by omega) hb1
  by_cases hb2 : cy.val < 6
  · exact receipt_row_07_band_y05 cy (by omega) hb2
  by_cases hb3 : cy.val < 7
  · exact receipt_row_07_band_y06 cy (by omega) hb3
  by_cases hb4 : cy.val < 8
  · exact receipt_row_07_band_y07 cy (by omega) hb4
  by_cases hb5 : cy.val < 12
  · exact receipt_row_07_b08 cy (by omega) hb5
  by_cases hb6 : cy.val < 16
  · exact receipt_row_07_b12 cy (by omega) hb6
  by_cases hb7 : cy.val < 20
  · exact receipt_row_07_b16 cy (by omega) hb7
  · exact receipt_row_07_b20 cy (by omega) (by omega)

theorem receipt_row_07 : RowReceipt 7 :=
  fastRowReceipt_to_rowReceipt 7 receipt_row_07_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
