import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07Hot08BPart01

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_07_band_12 : RowBandReceipt 7 14 22 := by
  intro cy hylo hyhi
  by_cases h_16 : cy.val < 16
  · exact receipt_row_07_band_12_a cy hylo h_16
  by_cases h_18 : cy.val < 18
  · exact receipt_row_07_band_12_b cy (by omega) h_18
  by_cases h_20 : cy.val < 20
  · exact receipt_row_07_band_12_c cy (by omega) h_20
  · exact receipt_row_07_band_12_d cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
