import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Band04Y02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_04 : RowBandReceipt 5 12 15 := by
  intro cy hylo hyhi
  by_cases h₀ : cy.val < 13
  · exact receipt_row_05_band_04_y_00 cy hylo h₀
  by_cases h₁ : cy.val < 14
  · exact receipt_row_05_band_04_y_01 cy (by omega) h₁
  · exact receipt_row_05_band_04_y_02 cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
