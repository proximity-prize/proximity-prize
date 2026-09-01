import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05Band03Y02

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_05_band_03 : RowBandReceipt 5 9 12 := by
  intro cy hylo hyhi
  by_cases h₀ : cy.val < 10
  · exact receipt_row_05_band_03_y_00 cy hylo h₀
  by_cases h₁ : cy.val < 11
  · exact receipt_row_05_band_03_y_01 cy (by omega) h₁
  · exact receipt_row_05_band_03_y_02 cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
