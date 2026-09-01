import ProximityPrize.SubmissionLower.LocatorReplacementGridRow15Band00Y02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_15_band_00 : RowBandReceipt 15 0 3 := by
  intro cy hylo hyhi
  by_cases h₀ : cy.val < 1
  · exact receipt_row_15_band_00_y_00 cy hylo h₀
  by_cases h₁ : cy.val < 2
  · exact receipt_row_15_band_00_y_01 cy (by omega) h₁
  · exact receipt_row_15_band_00_y_02 cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
