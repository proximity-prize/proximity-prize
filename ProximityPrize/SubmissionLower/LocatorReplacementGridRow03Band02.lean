import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03Band02Y21

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_row_03_band_02 : RowBandReceipt 3 14 22 := by
  intro cy hylo hyhi
  by_cases h₁₅ : cy.val < 15
  · exact receipt_row_03_band_02_y_14 cy hylo h₁₅
  by_cases h₁₆ : cy.val < 16
  · exact receipt_row_03_band_02_y_15 cy (by omega) h₁₆
  by_cases h₁₇ : cy.val < 17
  · exact receipt_row_03_band_02_y_16 cy (by omega) h₁₇
  by_cases h₁₈ : cy.val < 18
  · exact receipt_row_03_band_02_y_17 cy (by omega) h₁₈
  by_cases h₁₉ : cy.val < 19
  · exact receipt_row_03_band_02_y_18 cy (by omega) h₁₉
  by_cases h₂₀ : cy.val < 20
  · exact receipt_row_03_band_02_y_19 cy (by omega) h₂₀
  by_cases h₂₁ : cy.val < 21
  · exact receipt_row_03_band_02_y_20 cy (by omega) h₂₁
  · exact receipt_row_03_band_02_y_21 cy (by omega) hyhi

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
